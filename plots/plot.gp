set terminal latex

set xrange [0:2.1]
set title "Processor Time vs Term Size"
set xlabel "Input Size (millions of nodes)"
set ylabel "Processor Time (ms)"

plot '< cat -' with yerrorbars title "Benchmark Data"
