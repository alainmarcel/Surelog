#!/usr/bin/env python3

"""
Batch compare UHDM DB outputs. Useful to compare outputs generated by two CI builds.
"""

import argparse
import multiprocessing
import os
import platform
import pprint
import re
import shutil
import subprocess
import sys
import time
import traceback

from collections import OrderedDict
from contextlib import redirect_stdout, redirect_stderr
from datetime import datetime
from enum import Enum, unique
from pathlib import Path
from threading import Lock


_this_filepath = os.path.realpath(__file__)
_default_dbname = 'surelog.uhdm'


_log_mutex = Lock()
def log(text, end='\n'):
  _log_mutex.acquire()
  try:
    print(text, end=end, flush=True)
  finally:
    _log_mutex.release()


@unique
class Status(Enum):
  PASS = 0
  FAIL = -1
  MISSING = -2

  def __str__(self):
    return str(self.name)


def _mkdir(dirpath, retries=10):
  count = 0
  while count < retries:
    os.makedirs(dirpath, exist_ok=True)

    if os.path.exists(dirpath):
      return True

    count += 1
    time.sleep(0.1)

  return os.path.exists(dirpath)


def _rmdir(dirpath, retries=10):
  count = 0
  while count < retries:
    shutil.rmtree(dirpath, ignore_errors=True)

    if not os.path.exists(dirpath):
      return True

    count += 1
    time.sleep(0.1)

  shutil.rmtree(dirpath)
  return not os.path.exists(dirpath)


def _find_files(dirpath, pattern):
  return list(Path(dirpath).rglob(pattern))


def _is_filtered(name, filters):
  if not filters:
    return True

  for filter in filters:
    if isinstance(filter, str):
      if filter.lower() == name.lower():
        return True
    else:
      if filter.search(name):  # Note: match() reports success only if the match is at index 0
        return True

  return False


def _compare_one(params):
  start_dt = datetime.now()
  name, lhs_dirpath, rhs_dirpath, uhdm_cmp_filepath, output_dirpath = params

  log_filepath = os.path.join(output_dirpath, f'{name}.log')
  lhs_filepath = os.path.join(lhs_dirpath, name, _default_dbname)
  rhs_filepath = os.path.join(rhs_dirpath, name, _default_dbname)

  log(f'Comparing {name}')

  status = Status.FAIL
  with open(log_filepath, 'wt') as log_strm, redirect_stdout(log_strm), redirect_stderr(log_strm):
    lhs_exists = os.path.isfile(lhs_filepath)
    rhs_exists = os.path.isfile(rhs_filepath)

    print(f'start-time: {start_dt}')
    print( '')
    print( 'Environment:')
    print(f'             name: {name}')
    print(f'      lhs-dirpath: {lhs_dirpath}')
    print(f'     rhs-filepath: {rhs_dirpath}')
    print(f'uhdm_cmp-filepath: {uhdm_cmp_filepath}')
    print(f'   output-dirpath: {output_dirpath}')
    print(f'     lhs-filepath: {lhs_filepath}')
    print(f'     rhs-filepath: {rhs_filepath}')
    print(f'     log-filepath: {log_filepath}')
    print(f'       lhs-exists: {lhs_exists}')
    print(f'       rhs-exists: {rhs_exists}')
    print( '\n')

    if lhs_exists and rhs_exists:
      args = [uhdm_cmp_filepath, lhs_filepath, rhs_filepath]

      print(f'Launching uhdm-cmp with arguments:')
      pprint.pprint(args)
      print('\n', flush=True)

      try:
        result = subprocess.run(
            args,
            stdout=log_strm,
            stderr=subprocess.STDOUT,
            check=False,
            cwd=os.path.dirname(uhdm_cmp_filepath))
        print(f'uhdm-cmp terminated with exit code: {result.returncode}')
        status = Status.PASS if result.returncode == 0 else Status.FAIL
      except:
        status = Status.FAIL
        print(f'uhdm-cmp threw an exception with exit code: {result.returncode}')
        traceback.print_exc()
    else:
      print(f'Existence mismatch: lhs={lhs_exists}, rhs={rhs_exists}')
      status = Status.MISSING

    end_dt = datetime.now()
    delta = end_dt - start_dt
    print(f'end-time: {str(end_dt)} {str(delta)}', flush=True)

  return (name, status)


def _compare(args):
  lhs_filepaths = _find_files(args.lhs_dirpath, _default_dbname)
  rhs_filepaths = _find_files(args.rhs_dirpath, _default_dbname)

  test_names = set(Path(Path(filepath).parent).stem for filepath in lhs_filepaths + rhs_filepaths)

  params = [(
    name,
    args.lhs_dirpath,
    args.rhs_dirpath,
    args.uhdm_cmp_filepath,
    args.output_dirpath
  ) for name in test_names if _is_filtered(name, args.filters)]

  jobs = min(args.jobs, len(params))

  if jobs <= 1:
    results = [_compare_one(param) for param in params]
  else:
    with multiprocessing.Pool(processes=jobs) as pool:
      results = pool.map(_compare_one, params)

  return dict(results)


def _print_report(results):
  columns = ['TESTNAME', 'STATUS']

  rows = []
  summary = OrderedDict([(status.name, 0) for status in Status])
  for name, status in sorted(results.items(), key=lambda r: (-r[1].value, r[0])):
    summary[status.name] += 1
    rows.append([name, status.name])

  widths = [max([len(row[index]) for row in [columns] + rows]) for index in range(len(columns))]
  row_format = '| ' + ' | '.join([f'{{:{widths[i]}}}' for i in range(len(widths))]) + ' |'
  separator = '+-' + '-+-'.join(['-' * width for width in widths]) + '-+'

  print('')
  print('Results: ')
  print(separator)
  print(row_format.format(*columns))
  print(separator)
  for row in rows:
    print(row_format.format(*row))
  print(separator, flush=True)

  rows = [[k, str(v)] for k, v in summary.items()]
  widths = [max([len(str(row[index])) for row in rows]) for index in range(2)]
  row_format = '| ' + ' | '.join([f'{{:{width}}}' for width in widths]) + ' |'
  separator = '+-' + '-+-'.join(['-' * width for width in widths]) + '-+'

  print('')
  print('Summary: ')
  print(separator)
  for row in rows:
    print(row_format.format(*row))
  print(separator, flush=True)


def _main():
  start_dt = datetime.now()
  print(f'Starting UHDM Database Compare Regression Tests @ {str(start_dt)}')

  parser = argparse.ArgumentParser()
  parser.add_argument('lhs_dirpath', type=str, help='LHS directory containing uhdm DBs.')
  parser.add_argument('rhs_dirpath', type=str, help='RHS directory containing uhdm DBs.')

  parser.add_argument(
      '--uhdm-cmp-filepath', dest='uhdm_cmp_filepath', required=True, type=str, help='Location of uhdm-cmp executable')
  parser.add_argument(
      '--output-dirpath', dest='output_dirpath', required=True, type=str, help='Output directory path')

  parser.add_argument(
      '--filters', nargs='+', required=False, default=[], type=str,
      help='Filter comparing only matching these regex inputs')
  parser.add_argument(
      '--jobs', nargs='?', required=False, default=multiprocessing.cpu_count(), type=int,
      help='Run tests in parallel, optionally providing max number of concurrent processes. Set 0 to run sequentially.')
  args = parser.parse_args()

  args.uhdm_cmp_filepath = os.path.abspath(args.uhdm_cmp_filepath)
  args.output_dirpath = os.path.abspath(args.output_dirpath)

  if args.filters:
    filters = set()
    for filter in args.filters:
      if filter.startswith('@'):
        with open(filter[1:], 'rt') as strm:
          for line in strm:
            line = line.strip()
            if line:
              filters.add(line)
      else:
        filters.add(filter)
    args.filters = filters

  args.filters = [text if text.isalnum() else re.compile(text, re.IGNORECASE) for text in args.filters]

  if (args.jobs == None) or (args.jobs > multiprocessing.cpu_count()):
    args.jobs = multiprocessing.cpu_count()

  print( 'Environment:')
  print(f'              command-line: {" ".join(sys.argv)}')
  print(f'           current-dirpath: {os.getcwd()}')
  print(f'               lhs_dirpath: {args.lhs_dirpath}')
  print(f'               rhs_dirpath: {args.rhs_dirpath}')
  print(f'         uhdm-cmp-filepath: {args.uhdm_cmp_filepath}')
  print(f'            output-dirpath: {args.output_dirpath}')
  print(f'                   filters: {args.filters}')
  print(f'                      jobs: {args.jobs}')
  print( '\n\n')

  _mkdir(args.output_dirpath)


  print(f'Comparing UHDM Databases ...')
  results = _compare(args)

  failed_count = len([_ for _ in results.values() if _ != Status.PASS])
  compare_result = sum(_.value for _ in results.values() if _ != Status.PASS)
  print(f'Sucessfully compared {len(results)} databases with {failed_count} failures.')

  _print_report(results)

  end_dt = datetime.now()
  delta = round((end_dt - start_dt).total_seconds())

  print('')
  print(f'Surelog UHDM Database Compare Regression Test Completed @ {str(end_dt)} in {str(delta)} seconds')

  return compare_result


if __name__ == '__main__':
  sys.exit(_main())
