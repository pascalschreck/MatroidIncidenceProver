// fichier globals.h
#ifndef __GLOBALS_H__
#define __GLOBALS_H__
#include <stdbool.h>

extern unsigned dim;
extern const unsigned sizemyType;
extern unsigned realSizemyType;
extern bool debug_mode;
extern bool trace;
myType traced;

#define dft_statement_name "dft_statement.stat"
#define dft_rankoutput_name "dft_rankoutput.txt"
#define dft_coqoutput_name "dft_coqoutput.v"
#define dft_newrules_name "dft_newrules.txt"


#define stat_flag 1
#define rank_flag 2
#define coq_flag 4
#define rule_flag 8

/* macro pour le déboggage */
#define TAB  fputc('\t', debug_file)
#define NL	 fputc('\n', debug_file)
#define DEB_PS(str) fputs((str), debug_file)

#define SetFrom(MT) ((MT) & 0x3FFFFFFFFFFFFFF)

#endif