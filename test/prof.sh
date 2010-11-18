#!/bin/sh

# Script to exclude some patterns from code coverage given by mlprof

TMPFILE=$(mktemp -t exclude) || exit 1

grep -v -E -e '^#|^[:space:]*$' ./test/exclude.txt > $TMPFILE
EXCLUDE=""
while read l ; do
  EXCLUDE=$EXCLUDE$(echo $l\|)
done < $TMPFILE

EXCLUDE=$EXCLUDE"^ "
rm -f "$TMPFILE"

mlprof -raw true -show-line true ./test/main-prof ./test/run/mlmon.out \
| grep '(0)' \
| grep -v -E -e "$EXCLUDE" \
| grep -o -E -e '^.*: [[:digit:]]{1,5}' \
| sort \
| cat -n
