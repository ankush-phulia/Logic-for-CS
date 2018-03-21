# Assignment 2 : First Order Logic Resolution
<center>
##Logic for CS  


Ankush Phulia| 2014CS50279
---|


  </center>
  
  
 
### Structure

#### Symbols
Type | Symbols
----------------------|
Term  | CONST, VAR, FUNC
Form | TOP1, BOTTOM1, PRED, NOT1, AND1, OR1, IMP1, IFF1, ITE1, FORALL, EXISTS


#### Signature
> makePrenex : Form → Form


<!-- -->

>makePCNF  : Form → Form

<!-- -->

>makeSCNF : Form → Form

<!-- -->

>resolve : Form → bool

<!-- -->

### Algorithm
* The backchain algorithm for horn clauses is semi deterministic. It can go into infinite loops for some clauses which are satisfiable
* The completeness is defined for clauses which derive an empty clause.
If empty clause can be derived from the set of clauses, then an empty clause can be generated using backward chaining
* First, the formula is converted into prenex normal form, after which, the quantifier-free part is converted into conjunctive normal form, to obtain PCNF
* 'EXISTS' quantifiers are removed by the process of skolemization, and so PCNF is converted into SCNF, by introduction of new function symbols
* Unification is the crucial step for resolution, and is required to only be done for 2 clauses, specifically 2 literals (positive or negative predicate) at a time. Thus the 'unify' function is written to unify two terms, which is levraged to unify two predicates, and further, to obtain resolvent of two clauses
* Now, for resolution, the invariant is that empty clause can be derived only if there is some goal clause(a clause with all negative predicates) and some non-goal clause(a clause with one positive predicate) so this is the basic check
* If there are goal clauses and non goal clauses both, a DFS-type algorithm with one input as one of the goal clause, second input as set of non goal clauses and the final input as the height(this has to be maintained so that the program can be terminated at some point of time if an empty clause can't be generated over many iterations). 
* For one goal clause, a negative literal is taken and program clauses are searched to find a clause that can be resolved with this, and the first such clause is taken and resolvent is otained. SInce this resolvent is also a goal clause, the previous goal clause is updated, and the program clause is not deleted.
* Each resolve step increases the running depth by one, if no empty clause is derived by then, it is assumed to be satisfiable. Also if at any point, there are no progrm clauses, or no goal clauses, it is assumed satisfiable.




### Issues Faced

* Standardisation of variable during quantifier movement, so that a variable of the same name isn't bound twice in prenex form
* In CNF form, each of the clauses have a seperate set of variables, so that no issues arise during resolution-unification
* Depth of resolution, the DFS has to be stopped at some point as the process may go on indefinitely. It has been kept to 50.

### Conclusion
Each function makePrenex, makePCNF, makeSCNF, resolve is independent and can feed data to each other. 'resolve' returns true if the depth is met, or empty cnf is derived, or all program clauses/ goal clauses are eliminated. If and only if the empty clause can be derived, then false is returned.
