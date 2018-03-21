# Assignment 1 : Lexer-Parser
<center>
##Logic for CS  


Ankush Phulia| 2014CS50279
---|


  </center>
  
  
### Project Structure
* *sources.cm* - All pre-requisites for ml-lex and ml-yacc
* *PropLogic.lex* - Lexer for language with ml-lex
* *PropLogic.grm* - Grammar for creating parse with ml-yacc
* *PropLogic.sml* - Script to integrate lexer and parser
* *DataType.sml* - Signature and structure of AST and its methods
* *LexerParser.sml* - Script to take input file and write the output to a file
  
  
### Grammar

#### Symbols
Type | Symbols
----------------------|
Terminals           | TOP, BOTTOM, ATOM, WS, LPAR, RPAR, NOT, AND, OR, IFF, IF, THEN, ELSE
Non - Terminals | PROP, PROP1, PROP2, PROP3, PROP4, PROP5, PROP6, ATTO (a list of ATOMs)
Start		   | START

#### Production Rules
> START → PROP
<dd> | WS PROP

<!-- -->

>PROP → PROP1 *IFF* PROP 
<dd> | ( PROP ) 
<dd> | PROP1

<!-- -->

>PROP1 → *IF* PROP1 *THEN* PROP1
<dd>| *IF* PROP1 *THEN* PROP2 *ELSE* PROP1 
<dd>| PROP3 
<dd>| ( PROP )

<!-- -->

>PROP2 → *IF* PROP1 *THEN* PROP2 *ELSE* PROP2
<dd>| PROP3
<dd>| ( PROP )

<!-- -->

>PROP3 → PROP3 *OR* PROP4
<dd>| PROP4
<dd>| ( PROP )
		
<!-- -->

>PROP4 → PROP4 *AND* PROP5
<dd>| PROP5
<dd>| ( PROP )
		
<!-- -->

>PROP5 → *NOT* PROP5
<dd>| PROP6
<dd>| ( PROP )

<!-- -->

>PROP6 → *TOP* | *BOTTOM* | ATTO

<!-- -->

> ATTO → *ATOM* ATTO
<dd>| *ATOM* WS ATTO
<dd>| *ATOM* WS
<dd> | *ATOM*	

*Note* - "(" = LPAR and ")" = RPAR


#### Notes

* The grammar enforces priority of operators as specified, with *NOT* binding most tightly, and *IFF* the least (as per later discussions)
* The grammar is unambiguous, each each sentence in propositional logic has a unique derivation
* Spaces inside ATOMs are kept, while leading and trailing are discarded


### Sources Used
* [ML-Lex Manual](http://www.smlnj.org/doc/ML-Lex/manual.html) in *PropLogic.lex*
* [ML-Yacc Manual](https://www.cs.princeton.edu/~appel/modern/ml/ml-yacc/manual.html) in *PropLogic.grm*
* *Pi Language* [User Guide for ML-Yacc](http://www.cs.tufts.edu/comp/181/ug.pdf) in *PropLogic.sml*
* *IntExp Language* [CS235 Languages and Automata] in *PropLogic.sml*
* *Calculator Language* [ML-Yacc Examples] for *sources.cm*, *PropLogic.lex* and *PropLogic.grm***