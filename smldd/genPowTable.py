#!/usr/bin/env python3.1
# encoding: utf-8

import sys
import os

max_k = 2000
max_h = 2000

sml=\
"""
structure PowTable = struct
(*  This table stores the pre-computed result of k^h.
      1st column: k.
      2nd column: h.
      3rd column: k^h.
*)
val table =
[

{sml}
]

end (* structure PowTable *)
"""

line="( {k:d}, {h:d}, {pow:d} )\n"

def main():

  table_content=""
  size = 0
  first_line = True
  smlfile = open('./PowTable.sml','w')

  for k in range(1,max_k+1):
    for h in range(1,max_h+1):
      res = pow(k,h)
      if res <= 100000000 and res >= 10 and res != k:
        size += 1
        if first_line:
          table_content += "  " + line.format(k=k,h=h,pow=res)
          first_line = False
        else:
          table_content += ", " + line.format(k=k,h=h,pow=res)

  smlfile.write( sml.format( size=size , sml=table_content) )

if __name__ == '__main__':
	main()

