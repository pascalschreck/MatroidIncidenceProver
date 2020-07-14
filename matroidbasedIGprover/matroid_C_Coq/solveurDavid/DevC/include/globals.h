// fichier globals.h
#ifndef __GLOBALS_H__
#define __GLOBALS_H__

extern unsigned dim;
extern const unsigned sizemyType;
extern unsigned realSizemyType;

#define dft_statement_name "dft_statement.stat"
#define dft_rankoutput_name "dft_rankoutput.txt"
#define dft_coqoutput_name "dft_coqoutput.v"
#define dft_newrules_name "dft_newrules.txt"


#define stat_flag 1
#define rank_flag 2
#define coq_flag 4
#define rule_flag 8

#endif