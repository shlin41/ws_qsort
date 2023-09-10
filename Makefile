all:
	gcc -O2 -Wall -lpthread ws_qsort_v4.c -o v4
	gcc -O2 -Wall -lpthread ws_qsort_v5.c -o v5

