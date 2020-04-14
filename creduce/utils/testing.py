import asyncio
import difflib
import filecmp
import importlib.util
import logging
import math
import multiprocessing
import os
import os.path
import platform

# Currently the resource module is only available on Unix based systems
try:
    import resource
    # We're nice here and only open up to half of the allowed number of files
    MAX_OPEN_FILES = resource.getrlimit(resource.RLIMIT_NOFILE)[0] / 2
except ImportError:
    # Just assume that we might be able to open up to 1024 files
    MAX_OPEN_FILES = 1024

import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import weakref

import concurrent.futures
from concurrent.futures import wait, FIRST_COMPLETED
from pebble import ProcessPool

from .. import CReduce
from creduce.passes.abstract import AbstractPass

from . import compat
from . import readkey
from .error import InsaneTestCaseError
from .error import InvalidInterestingnessTestError
from .error import InvalidTestCaseError
from .error import PassBugError
from .error import ZeroSizeError

class TestEnvironment:
    def __init__(self, test_script, timeout, save_temps, order):
        self.test_case = None
        self.additional_files = set()
        self.state = None
        self._dir = tempfile.mkdtemp(prefix="creduce-")
        self.timeout = timeout
        self.save_temps = save_temps
        self._base_size = None
        self.test_script = test_script
        self.__exitcode = None
        self.__process = None
        self.order = order

# TODO
#        if not save_temps:
#            self._finalizer = weakref.finalize(self, self._cleanup, self.path)

    def __enter__(self):
        return self

    def __exit__(self, exc, value, tb):
        if not self.save_temps:
            self.cleanup()

    @classmethod
    def _cleanup(cls, name):
        try:
            # TODO: remove
            assert 'creduce-' in name and 'tmp' in name
            shutil.rmtree(name)
        except FileNotFoundError:
            pass

    def cleanup(self):
        if self._finalizer.detach():
            self._cleanup(self.path)

    def copy_files(self, test_case, additional_files):
        if test_case is not None:
            self.test_case = os.path.basename(test_case)
            shutil.copy(test_case, self.path)
            self._base_size = os.path.getsize(test_case)

        for f in additional_files:
            self.additional_files.add(os.path.basename(f))
            shutil.copy(f, self.path)

    @property
    def size_improvement(self):
        if self._base_size is None:
            return None
        else:
            return (self._base_size - os.path.getsize(self.test_case_path))

    @property
    def path(self):
        return self._dir

    @property
    def test_case_path(self):
        return os.path.join(self.path, self.test_case)

    @property
    def additional_files_paths(self):
        return [os.path.join(self.path, f) for f in self.additional_files]

    def dump(self, dst):
        if self.test_case is not None:
            shutil.copy(self.test_case_path, dst)

        for f in self.additional_files:
            shutil.copy(f, dst)

        shutil.copy(self.test_script, dst)

    def run_test(self):
        cmd = [self.test_script]
        if self.test_case is not None:
            cmd.append(self.test_case_path)
        cmd.extend(self.additional_files_paths)

        return subprocess.run(cmd, cwd=self.path, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

class TestRunner:
    def __init__(self, test_script, timeout, save_temps):
        self.test_script = os.path.abspath(test_script)
        if not self.is_valid_test(test_script):
            raise InvalidInterestingnessTestError(test)

        self.timeout = timeout
        self.save_temps = save_temps

    @classmethod
    def is_valid_test(cls, test_script):
        for mode in {os.F_OK, os.X_OK}:
            if not os.access(test_script, mode):
                return False
        return True

    def create_environment(self, order):
        return TestEnvironment(self.test_script, self.timeout, self.save_temps, order)

class TestManager:
    GIVEUP_CONSTANT = 50000
    MAX_CRASH_DIRS = 10
    MAX_EXTRA_DIRS = 25000
    MAX_FUTURES = 16

    def __init__(self, test_runner, pass_statistic, test_cases, parallel_tests, no_cache, skip_key_off, silent_pass_bug, die_on_pass_bug, print_diff, max_improvement, no_give_up, also_interesting):
        self.test_runner = test_runner
        self.pass_statistic = pass_statistic
        self.test_cases = set()
        self.parallel_tests = parallel_tests
        self.no_cache = no_cache
        self.skip_key_off = skip_key_off
        self.silent_pass_bug = silent_pass_bug
        self.die_on_pass_bug = die_on_pass_bug
        self.print_diff = print_diff
        self.max_improvement = max_improvement
        self.no_give_up = no_give_up
        self.also_interesting = also_interesting

        for test_case in test_cases:
            self._check_file_permissions(test_case, [os.F_OK, os.R_OK, os.W_OK], InvalidTestCaseError)
            self.test_cases.add(os.path.abspath(test_case))

        self._orig_total_file_size = self.total_file_size
        self._cache = {}

    @property
    def total_file_size(self):
        return self._get_file_size(self.test_cases)

    @property
    def sorted_test_cases(self):
        return sorted(self.test_cases, key=os.path.getsize)

    @staticmethod
    def _get_file_size(files):
        return sum(os.path.getsize(f) for f in files)

    def backup_test_cases(self):
        for f in self.test_cases:
            orig_file = "{}.orig".format(os.path.splitext(f)[0])

            if not os.path.exists(orig_file):
                # Copy file and preserve attributes
                shutil.copy2(f, orig_file)

    @staticmethod
    def _check_file_permissions(path, modes, error):
        for m in modes:
            if not os.access(path, m):
                if error is not None:
                    raise error(path, m)
                else:
                    return False

        return True

    @staticmethod
    def _get_extra_dir(prefix, max_number):
        for i in range(0, max_number + 1):
            digits = int(round(math.log10(max_number), 0))
            extra_dir = ("{0}{1:0" + str(digits) + "d}").format(prefix, i)

            if not os.path.exists(extra_dir):
                break

        # just bail if we've already created enough of these dirs, no need to
        # clutter things up even more...
        if os.path.exists(extra_dir):
            return None

        return extra_dir

    def _report_pass_bug(self, test_env, problem):
        if not self.die_on_pass_bug:
            logging.warning("{} has encountered a non fatal bug: {}".format(self._pass, problem))

        crash_dir = self._get_extra_dir("creduce_bug_", self.MAX_CRASH_DIRS)

        if crash_dir == None:
            return

        os.mkdir(crash_dir)
        test_env.dump(crash_dir)

        if not self.die_on_pass_bug:
            logging.debug("Please consider tarring up {} and mailing it to creduce-bugs@flux.utah.edu and we will try to fix the bug.".format(crash_dir))

        with open(os.path.join(crash_dir, "PASS_BUG_INFO.TXT"), mode="w") as info_file:
            info_file.write("{}\n".format(CReduce.Info.PACKAGE_STRING))
            info_file.write("{}\n".format(CReduce.Info.GIT_VERSION))
            info_file.write("{}\n".format(platform.uname()))
            info_file.write(PassBugError.MSG.format(self._pass, problem, crash_dir))

        if self.die_on_pass_bug:
            raise PassBugError(self._pass, problem, crash_dir)

    @staticmethod
    def _diff_files(orig_file, changed_file):
        with open(orig_file, mode="r") as f:
            orig_file_lines = f.readlines()

        with open(changed_file, mode="r") as f:
            changed_file_lines = f.readlines()

        diffed_lines = difflib.unified_diff(orig_file_lines, changed_file_lines, orig_file, changed_file)

        return "".join(diffed_lines)

    def check_sanity(self):
        logging.debug("perform sanity check... ")

        test_env = self.test_runner.create_environment(0)

        logging.debug("sanity check tmpdir = {}".format(test_env.path))

        test_env.copy_files(None, self.test_cases)

        p = test_env.run_test()
        if not p.returncode:
            logging.debug("sanity check successful")
        else:
            raise InsaneTestCaseError(self.test_cases, p.args)

    def create_and_run_test_env(self, state, order):
        test_env = self.test_runner.create_environment(order)
        # Copy files from base env
        test_env.copy_files(self._base_test_env.test_case_path, self._base_test_env.additional_files_paths)
        # Copy state from base_env
        test_env.state = state

        # transform by state
        (result, test_env.state) = self._pass.transform(test_env.test_case_path, test_env.state)
        if result != self._pass.Result.ok:
            return (result, test_env)

        # run test script
        p = test_env.run_test()
        self.__exitcode = p.returncode

        return (self._pass.Result.ok if self.__exitcode == 0 else self._pass.Result.invalid, test_env)

    def run_parallel_tests(self):
        with ProcessPool(max_workers=self.parallel_tests) as pool:
            futures = []
            order = 1
            while self._base_test_env.state != None:
                # do not create too many states
                if len(futures) >= self.MAX_FUTURES:
                    wait(futures, return_when=FIRST_COMPLETED)

                done = set([future for future in futures if future.done()])
                candidate = None
                for future in done:
                    (result, test_env) = future.result()
                    if result == self._pass.Result.ok or result == self._pass.Result.stop or result == self._pass.Result.error:
                        candidate = future
                        break

                # wait for all before the candidate
                if candidate:
                    joined_count = 0
                    for f in futures[:futures.index(candidate)]:
                        f.result()
                        (result, _) = future.result()
                        # TODO: add method for it
                        if result == self._pass.Result.ok or result == self._pass.Result.stop or result == self._pass.Result.error:
                            break

                    # we joined all futures before the candidate, let's close the pool
                    pool.close()
                    pool.stop()
                    return futures

                futures = [f for f in futures if not f in done]
                futures.append(pool.schedule(self.create_and_run_test_env, (self._base_test_env.state, order)))
                order += 1
                state = self._pass.advance(self._base_test_env.test_case_path, self._base_test_env.state)
                # we are at the end of enumeration
                if state == None:
                    pool.close()
                    pool.join()
                    return futures
                else:
                    self._base_test_env.state = state

            assert False

    def run_pass(self, pass_):
        self._pass = pass_

        logging.info("===< {} >===".format(self._pass))

        if self.total_file_size == 0:
            raise zerosizeerror(self.test_cases)

        for test_case in self.test_cases:
            self._current_test_case = test_case

            if self._get_file_size([test_case]) == 0:
                continue

            if not self.no_cache:
                with open(test_case, mode="r+") as tmp_file:
                    test_case_before_pass = tmp_file.read()

                    pass_key = repr(self._pass)

                    if (pass_key in self._cache and
                        test_case_before_pass in self._cache[pass_key]):
                        tmp_file.seek(0)
                        tmp_file.truncate(0)
                        tmp_file.write(self._cache[pass_key][test_case_before_pass])
                        logging.info("cache hit for {}".format(test_case))
                        continue

            # Create initial test environment
            self._base_test_env = self.test_runner.create_environment(0)
            self._base_test_env.copy_files(test_case, self.test_cases ^ {test_case})
            self._base_test_env.state = self._pass.new(self._base_test_env.test_case_path)

            self._stopped = (self._base_test_env.state is None)
            self._skip = False
            self._since_success = 0

            if not self.skip_key_off:
                logger = readkey.KeyLogger()

            while not self._stopped and not self._skip:
                # Ignore more key presses after skip has been detected
                if not self.skip_key_off and not self._skip:
                    if logger.pressed_key() == "s":
                        self._skip = True
                        logging.info("****** skipping the rest of this pass ******")

                # TODO: XXX
                parallel_tests = self.run_parallel_tests()
                finished = [future for future in parallel_tests if future.done() and not future.cancelled()]
                if not finished:
                    return

                candidates = [f.result()[1] for f in finished if f.result()[0] == self._pass.Result.ok]
                candidates = sorted(candidates, key = lambda c: c.order)
                if candidates:
                    self.process_result(candidates[0])
                else:
                    return

    def process_result(self, test_env):
        logging.debug("Process result")

        self._base_test_env = test_env
        shutil.copy(test_env.test_case_path, self._current_test_case)
        state = self._pass.advance_on_success(test_env.test_case_path, self._base_test_env.state)

        if state is not None:
            self._base_test_env.state = state
        self._stopped = (state is None)
        self._since_success = 0
        self.pass_statistic.update(self._pass, success=True)

        pct = 100 - (self.total_file_size * 100.0 / self._orig_total_file_size)
        logging.info("({}%, {} bytes)".format(round(pct, 1), self.total_file_size))
