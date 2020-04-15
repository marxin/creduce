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
import weakref

import concurrent.futures
from concurrent.futures import wait, FIRST_COMPLETED
from pebble import ProcessPool

from .. import CReduce
from creduce.passes.abstract import AbstractPass, PassResult

from . import compat
from . import readkey
from .error import InsaneTestCaseError
from .error import InvalidInterestingnessTestError
from .error import InvalidTestCaseError
from .error import PassBugError
from .error import ZeroSizeError

class TestEnvironment:
    def __init__(self, test_script, timeout, save_temps, order, folder):
        self.test_case = None
        self.additional_files = set()
        self.state = None
        self.folder = folder
        self.timeout = timeout
        self.save_temps = save_temps
        self.base_size = None
        self.test_script = test_script
        self.exitcode = None
        self.result = None
        self.order = order

    def __enter__(self):
        return self
    def copy_files(self, test_case, additional_files):
        if test_case is not None:
            self.test_case = os.path.basename(test_case)
            shutil.copy(test_case, self.folder)
            self.base_size = os.path.getsize(test_case)

        for f in additional_files:
            self.additional_files.add(os.path.basename(f))
            shutil.copy(f, self.folder)

    @property
    def size_improvement(self):
        if self.base_size is None:
            return None
        else:
            return (self.base_size - os.path.getsize(self.test_case_path))

    @property
    def test_case_path(self):
        return os.path.join(self.folder, self.test_case)

    @property
    def additional_files_paths(self):
        return [os.path.join(self.folder, f) for f in self.additional_files]

    @property
    def success(self):
        return self.result == PassResult.OK and self.exitcode == 0

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

        return subprocess.run(cmd, cwd=self.folder, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

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

    def create_environment(self, order, folder):
        return TestEnvironment(self.test_script, self.timeout, self.save_temps, order, folder)

class TestManager:
    GIVEUP_CONSTANT = 50000
    MAX_CRASH_DIRS = 10
    MAX_EXTRA_DIRS = 25000
    MAX_FUTURES = 4

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

        # TODO: release
        folder = tempfile.mkdtemp(prefix="creduce-")
        test_env = self.test_runner.create_environment(0, folder)

        logging.debug("sanity check tmpdir = {}".format(test_env.folder))

        test_env.copy_files(None, self.test_cases)

        p = test_env.run_test()
        if not p.returncode:
            logging.debug("sanity check successful")
        else:
            raise InsaneTestCaseError(self.test_cases, p.args)

    def create_and_run_test_env(self, state, order, folder):
        test_env = self.test_runner.create_environment(order, folder)
        test_env.copy_files(self.current_test_case, self.test_cases ^ {self.current_test_case})
        test_env.state = state

        # transform by state
        (result, test_env.state) = self._pass.transform(test_env.test_case_path, test_env.state)
        test_env.result = result
        if test_env.result != PassResult.OK:
            return test_env

        # run test script
        p = test_env.run_test()
        test_env.exitcode = p.returncode
        return test_env

    @classmethod
    def release_folder(cls, future, temporary_folders):
        name = temporary_folders.pop(future)
        try:
            # TODO: remove
            assert 'creduce-' in name and 'tmp' in name
            shutil.rmtree(name)
        except FileNotFoundError:
            pass

    @classmethod
    def release_folders(cls, futures, temporary_folders):
        for future in futures:
            cls.release_folder(future, temporary_folders)
        assert not any(temporary_folders)

    def process_done_futures(self, futures, temporary_folders):
        have_candidate = False
        new_futures = []
        for future in futures:
            if future.done():
                if future.exception():
                    # TODO
                    print(str(future.exception()))
                    asdf
                test_env = future.result()
                if test_env.success:
                    # TODO check for max_improvement
                    # TODO check for size change
                    have_candidate = True
                    new_futures.append(future)
                else:
                    if test_env.result == PassResult.OK:
                        assert test_env.exitcode
                        # TODO: also interesting check
                    elif test_env.result == PassResult.STOP:
                        # TODO: stop it
                        have_candidate = True
                    elif test_env.result == PassResult.ERROR:
                        # TODO: report error
                        assert False
                    else:
                        # TODO: test_env.order GIVEUP
                        pass
                    # TODO
                    self.release_folder(future, temporary_folders)
            else:
                new_futures.append(future)

        return (have_candidate, new_futures)

    def wait_for_first_success(self, futures):
        for future in futures:
            test_env = future.result()
            if test_env.success:
                return test_env
        return None

    @classmethod
    def terminate_all(cls, pool):
        pool.stop()
        pool.join()

    def run_parallel_tests(self):
        with ProcessPool(max_workers=self.parallel_tests) as pool:
            futures = []
            temporary_folders = {}
            order = 1
            while self.state != None:
                # do not create too many states
                if len(futures) >= self.MAX_FUTURES:
                    wait(futures, return_when=FIRST_COMPLETED)

                (have_candidate, futures) = self.process_done_futures(futures, temporary_folders)
                if have_candidate:
                    success = self.wait_for_first_success(futures)
                    self.terminate_all(pool)
                    return (success, futures, temporary_folders)

                folder = tempfile.mkdtemp(prefix="creduce-")
                future = pool.schedule(self.create_and_run_test_env, [self.state, order, folder])
                temporary_folders[future] = folder
                futures.append(future)
                order += 1
                state = self._pass.advance(self.current_test_case, self.state)
                # we are at the end of enumeration
                if state == None:
                    success = self.wait_for_first_success(futures)
                    self.terminate_all(pool)
                    return (success, futures, temporary_folders)
                else:
                    self.state = state

    def run_pass(self, pass_):
        self._pass = pass_
        self.futures = []

        logging.info("===< {} >===".format(self._pass))

        if self.total_file_size == 0:
            raise zerosizeerror(self.test_cases)

        for test_case in self.test_cases:
            self.current_test_case = test_case

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

            # create initial state
            self.state = self._pass.new(self.current_test_case)
            self._skip = False
            self._since_success = 0

            if not self.skip_key_off:
                logger = readkey.KeyLogger()

            while self.state != None and not self._skip:
                # Ignore more key presses after skip has been detected
                if not self.skip_key_off and not self._skip:
                    if logger.pressed_key() == "s":
                        self._skip = True
                        logging.info("****** skipping the rest of this pass ******")

                success_env, futures, temporary_folders = self.run_parallel_tests()
                if not success_env:
                    return

                self.process_result(success_env)
                self.release_folders(futures, temporary_folders)

    def process_result(self, test_env):
        logging.debug("Process result")

        shutil.copy(test_env.test_case_path, self.current_test_case)

        self.state = self._pass.advance_on_success(test_env.test_case_path, test_env.state)
        self._since_success = 0
        self.pass_statistic.update(self._pass, success=True)

        pct = 100 - (self.total_file_size * 100.0 / self._orig_total_file_size)
        logging.info("({}%, {} bytes)".format(round(pct, 1), self.total_file_size))
