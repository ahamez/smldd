#!/bin/sh

# Script to exclude some patterns from code coverage given by mlprof

grep -v '^#' ./test/exclude.txt | grep -v '^[:space:]*$' > .tmp
EXCLUDE=""
while read l ; do
  EXCLUDE=$EXCLUDE$(echo $l\|)
done < .tmp

EXCLUDE=$EXCLUDE"^ "
rm -f .tmp

mlprof -raw true -show-line true ./test/main-prof ./test/run/mlmon.out \
| grep '(0)' \
| grep -v -E -e "$EXCLUDE" \
| grep -o -E -e '^.*: [[:digit:]]{1,5}' \
| sort
