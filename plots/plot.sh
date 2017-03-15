#!/bin/sh

egrep "benchmarking|mean" bench.log | paste -s -d ' \n' | tr '/' ' ' | tr -d '(' | awk '{printf("%s\t%s\t%s\t%s\n", $3, $5, $7, $10);}' | gnuplot plot.gp > plot.latex
