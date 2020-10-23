CFLAGS = -g -Wall
IFLAGS = -Iinclude 
DFLAG =  
OPATH = obj/

vpath %.h include
vpath %.c src
vpath %.o obj
vpath main bin

all : main

init :
	mkdir obj/
	mkdir bin/

main : main.o parties.o graph.o set.o maths_addon.o statement.o fprintthings.o
	gcc $(CFLAGS) -o main $(OPATH)main.o $(OPATH)parties.o $(OPATH)graph.o $(OPATH)set.o $(OPATH)statement.o $(OPATH)fprintthings.o -lm 
	mv $@ bin/

main.o : parties.h graph.h set.h statement.h globals.h
statement.o : statement.h globals.h
fprintthings.o : fprintthings.h parties.h graph.h set.h
parties.o : parties.h graph.h set.h globals.h
graph.o : set.h
set.o : set.h


%.o : %.c
	gcc $(CFLAGS) $(DFLAG) -c $< $(IFLAGS) $()
	mv $@ $(OPATH)

clean : 
	rm obj/* bin/*

archive : 
	tar -f code.tar.gz -cvz src/* include/* Makefile README.md quickstart.md

