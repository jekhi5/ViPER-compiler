#! /usr/bin/env python3
from pathlib import Path
from glob import glob
import argparse

"""
Looks at all `.fdl` files in the directory.
Splits them on a delimiter. Places everything past the delimiter into an out file.

Example:

test1.fdl:
    add1(2 + 3)
    ;
    6

=>

test1.fdl:
    add1(2 + 3)

test1.out:
    6
"""


def walk_dir(delimiter=r"@", dirname: str = ".", filetype=".fdl", verbose=0) -> None:
    if verbose > 0:
        print("Generating test files...")

    delimiter = f"\n{delimiter}\n"
    for filepath in glob(f"**/*{filetype}", root_dir=dirname):
        testfile = dirname / Path(filepath)
        if "do_err" in str(testfile) or "dont_err" in str(testfile):
            suffix = ".err"
        else:
            suffix = ".out"

        resultfile = testfile.with_suffix(suffix)
        if resultfile.exists():
            if verbose > 1:
                print(f"{str(testfile):.<50}{str(resultfile)} already exists.")
        else:
            if verbose > 0:
                print(f"{str(testfile):.<50}", end="")
            with open(testfile, "r+") as tf:
                contents = tf.read()
                test, result = contents.split(delimiter, maxsplit=1)
                tf.seek(0)
                tf.write(test)
                tf.truncate()

            with open(resultfile, "w") as rf:
                rf.write(result)
            if verbose > 0:
                print(f"{str(resultfile)} generated!")


def main(args):
    walk_dir(
        delimiter=args.splitter,
        dirname=args.dir,
        verbose=args.verbose,
        filetype=args.filetype,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("-d", "--dir", type=str, default="input/")
    parser.add_argument("-s", "--splitter", type=str, default=r"@")
    parser.add_argument("-v", "--verbose", type=int, default=0)
    parser.add_argument("-f", "--filetype", type=str, default=".fdl")

    args = parser.parse_args()
    main(args)
