CFLAGS = -g -Wall
IFLAGS = -Iinclude 
OPATH = obj/

vpath %.h include
vpath %.c src
vpath %.o obj
vpath main bin

all : main explore


init :
	mkdir obj/
	mkdir bin/

main : main.o parties.o graph.o set.o maths_addon.o statement.o fprintthings.o
	gcc $(CFLAGS) -o main $(OPATH)main.o $(OPATH)parties.o $(OPATH)graph.o $(OPATH)set.o $(OPATH)maths_addon.o $(OPATH)statement.o $(OPATH)fprintthings.o -lm 
	mv $@ bin/

explore : explore.o parties.o graph.o set.o maths_addon.o statement.o fprintthings.o
	gcc $(CFLAGS) -o explore $(OPATH)explore.o $(OPATH)parties.o $(OPATH)graph.o $(OPATH)set.o $(OPATH)maths_addon.o $(OPATH)statement.o $(OPATH)fprintthings.o -lm 
	mv $@ bin/

main.o : parties.h graph.h set.h maths_addon.h statement.h
explore.o : parties.h graph.h set.h maths_addon.h statement.h
statement.o : statement.h
fprintthings.o : fprintthings.h parties.h graph.h set.h maths_addon.h
DLrule.o : parties.h graph.h set.h maths_addon.h
parties.o : parties.h graph.h set.h maths_addon.h 
graph.o : set.h maths_addon.h
set.o : set.h
maths_addon.o : maths_addon.h


%.o : %.c
	gcc $(CFLAGS) -c $< $(IFLAGS)
	mv $@ $(OPATH)

geany :
	geany src/* include/* Makefile &

clean : 
	rm obj/* bin/*

archive : 
	tar -f code.tar.gz -cvz src/* include/* makefile

