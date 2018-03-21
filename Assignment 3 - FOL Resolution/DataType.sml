Control.Print.printDepth := 100;

signature FOL = 
sig
	datatype Term = CONST of string
					| VAR of string
					| FUNC of string * Term list

	datatype Form = TOP1
					| PRED of string * Term list
					| AND1 of Form * Form
					| IMP1 of Form * Form
					| ITE1 of Form * Form * Form
					| FORALL of string * Form
					| EXISTS of string * Form
					| BOTTOM1
					| NOT1 of Form
					| OR1 of Form * Form
					| IFF1 of Form * Form

	datatype Lit = P of string * (Term list)
				| N of string * (Term list)

	datatype Clause = CLS of (Lit list)

    datatype Cnf = CNF of (Clause list)

	val makePrenex : Form -> Form
	val makePCNF : Form -> Form
	val makeSCNF : Form -> Form
	val resolve : Form -> bool

end;

structure FOL = 
struct
	datatype Term = CONST of string
					| VAR of string
					| FUNC of string * Term list

	datatype Form = TOP1
					| BOTTOM1
					| PRED of string * Term list
					| NOT1 of Form
					| AND1 of Form * Form
					| OR1 of Form * Form
					| IMP1 of Form * Form
					| ITE1 of Form * Form * Form
					| IFF1 of Form * Form
					| FORALL of string * Form
					| EXISTS of string * Form

	datatype Lit = P of string * (Term list)
				| N of string * (Term list)

	datatype Clause = CLS of (Lit list)

	datatype Cnf = CNF of (Clause list)

	fun or (x, y) = x orelse y;

	fun negate (TOP1) = BOTTOM1
		| negate (BOTTOM1) = TOP1
		| negate (PRED(p, tl)) = NOT1(PRED(p, tl))
		| negate (NOT1(x)) = x
        | negate (AND1(x, y)) = OR1(negate(x), negate(y))
        | negate (OR1(x, y)) = AND1(negate(x), negate(y))
        | negate (FORALL(x, form)) = EXISTS(x, negate(form))
        | negate (EXISTS(x, form)) = FORALL(x, negate(form));

   	fun pushNeg (TOP1) = TOP1
		| pushNeg (BOTTOM1) = BOTTOM1
		| pushNeg (PRED(p, tl)) = PRED(p, tl)
		| pushNeg (NOT1(x)) = negate(x)
        | pushNeg (AND1(x, y)) = AND1(pushNeg(x), pushNeg(y))
        | pushNeg (OR1(x, y)) = OR1(pushNeg(x), pushNeg(y))
        | pushNeg (FORALL(x, form)) = FORALL(x, pushNeg(form))
        | pushNeg (EXISTS(x, form)) = EXISTS(x, pushNeg(form));

    fun removeI (PRED(x, tl)) = PRED(x, tl)
        | removeI (TOP1) = TOP1
        | removeI (BOTTOM1) = BOTTOM1
        | removeI (NOT1(x)) = NOT1(removeI(x))
        | removeI (AND1(x, y)) = AND1(removeI(x), removeI(y))
        | removeI (OR1(x, y)) = OR1(removeI(x), removeI(y))
        | removeI (FORALL(x, form)) = FORALL(x, removeI(form))
        | removeI (EXISTS(x, form)) = EXISTS(x, removeI(form))
        | removeI (IMP1(x, y)) = OR1(negate(removeI(x)), removeI(y))
        | removeI (IFF1(x, y)) = 
            let 
                val x_clean = removeI(x);
                val y_clean = removeI(y);
            in AND1(OR1(negate(x_clean), y_clean), OR1(negate(y_clean), x_clean))
            end
        | removeI (ITE1(x, y, z)) = 
            let 
                val x_clean = removeI(x);
            in OR1(AND1(x_clean, removeI(y)), AND1(negate(x_clean), removeI(z)))
            end;

	fun substituteTerm (y:Term) x (CONST(z)) = CONST(z)
		| substituteTerm (y:Term) x (VAR(z)) = if (z = x) then y else VAR(z)
		| substituteTerm y x (FUNC(a, tl)) = FUNC(a, (List.map (substituteTerm y x) tl));

	fun substitute (y:Term) x (TOP1) = TOP1
		| substitute y x (BOTTOM1) = BOTTOM1
		| substitute y x (PRED(a, tl)) = PRED(a, (List.map (substituteTerm y x) tl))
		| substitute y x (NOT1(z)) = NOT1(substitute y x z)
		| substitute y x (AND1(a, b)) = AND1((substitute y x a), (substitute y x b))
		| substitute y x (OR1(a, b)) = OR1((substitute y x a), (substitute y x b))
		| substitute y x (IMP1(a, b)) = IMP1((substitute y x a), (substitute y x b))
		| substitute y x (IFF1(a, b)) = IFF1((substitute y x a), (substitute y x b))
		| substitute y x (ITE1(a, b, c)) = ITE1((substitute y x a), (substitute y x b), (substitute y x c))
		| substitute y x (FORALL(a, form)) = if (x = a) then FORALL(a, form) else FORALL(a, (substitute y x form))
		| substitute y x (EXISTS(a, form)) = if (x = a) then EXISTS(a, form) else EXISTS(a, (substitute y x form));

	fun standarize suffix (FORALL(a, form)) = FORALL(a ^ suffix, (substitute (VAR(a ^ suffix)) a (standarize (suffix ^ ".1") form)) )
		| standarize suffix (EXISTS(a, form)) = EXISTS(a ^ suffix, (substitute (VAR(a ^ suffix)) a (standarize (suffix ^ ".1") form) ) )
		| standarize suffix (TOP1) = TOP1
		| standarize suffix (BOTTOM1) = BOTTOM1
		| standarize suffix (PRED(a, tl)) = PRED(a, tl)
		| standarize suffix (NOT1(x)) = NOT1(standarize (suffix ^ ".1") x)
		| standarize suffix (AND1(x, y)) = AND1((standarize (suffix ^ ".1") x), (standarize (suffix ^ ".2") y))
		| standarize suffix (OR1(x, y)) = OR1((standarize (suffix ^ ".1") x), (standarize (suffix ^ ".2") y))
		| standarize suffix (IMP1(x, y)) = IMP1((standarize (suffix ^ ".1") x), (standarize (suffix ^ ".2") y))
		| standarize suffix (IFF1(x, y)) = IFF1((standarize (suffix ^ ".1") x), (standarize (suffix ^ ".2") y))
		| standarize suffix (ITE1(x, y, z)) = ITE1((standarize (suffix ^ ".1") x), (standarize (suffix ^ ".2") y), (standarize (suffix ^ ".3") z))

	fun pullQuant (TOP1) = (TOP1, [])
		| pullQuant (BOTTOM1) = (BOTTOM1, [])
		| pullQuant (PRED(a, tl)) = (PRED(a, tl), [])
		| pullQuant (NOT1(a)) = (NOT1(a), []) (* assume NOTs near leaves*)
		| pullQuant (FORALL(x, form)) =
			let val (form1, quants) = pullQuant form in (form1, (quants @ [FORALL(x, TOP1)]) ) end
		| pullQuant (EXISTS(x, form)) = 
			let val (form1, quants) = pullQuant form in (form1, (quants @ [EXISTS(x, TOP1)]) ) end
		| pullQuant (AND1(a, b)) = 
			let
				val (form1, quants1) = pullQuant a;
				val (form2, quants2) = pullQuant b;
			in (AND1(form1, form2), quants2 @ quants1) end
		| pullQuant (OR1(a, b)) =
			let
				val (form1, quants1) = pullQuant a;
				val (form2, quants2) = pullQuant b;
			in (OR1(form1, form2), quants2 @ quants1) end
		| pullQuant (IMP1(a, b)) =
			let
				val (form1, quants1) = pullQuant a;
				val (form2, quants2) = pullQuant b;
			in (IMP1(form1, form2), quants2 @ quants1) end
		| pullQuant (IFF1(a, b)) =
			let
				val (form1, quants1) = pullQuant a;
				val (form2, quants2) = pullQuant b;
			in (IFF1(form1, form2), quants2 @ quants1) end
		| pullQuant (ITE1(a, b, c)) = 
			let
				val (form1, quants1) = pullQuant a;
				val (form2, quants2) = pullQuant b;
				val (form3, quants3) = pullQuant c;
			in (ITE1(form1, form2, form3), quants3 @ quants2 @ quants1) end;

	fun prenex form [] = form
		| prenex form ((FORALL(x,TOP1))::xs) = prenex (FORALL(x, form)) xs
		| prenex form ((EXISTS(x,TOP1))::xs) = prenex (EXISTS(x, form)) xs;

	fun makePrenex form = 
		let 
			val nnf = pushNeg (removeI form);
			val standard = standarize "" nnf;
			val (qff, quants) = pullQuant standard;
		in  prenex qff quants
		end;


    fun distOR (x, AND1(y, z)) = AND1((distOR(x, y)), (distOR(x, z)))
    	| distOR (AND1(x, y), z) = AND1(distOR(x, z), distOR(y, z))
    	| distOR (x, y) = OR1(x, y);

    fun distributeOR (PRED(a, tl)) = (PRED(a, tl))
    	| distributeOR (TOP1) = TOP1
    	| distributeOR (BOTTOM1) = BOTTOM1
    	| distributeOR (NOT1(x)) = NOT1(x)
    	| distributeOR (AND1(x, y)) = AND1((distributeOR x), (distributeOR y))
    	| distributeOR (OR1(x, y)) = distOR(x, y);

	fun makePCNF form = 
		let 
			val nnf = pushNeg (removeI form);
			val standard = standarize "" nnf;
			val (qff, quants) = pullQuant standard;
			val qfcnf = distributeOR qff;
		in  prenex qfcnf quants
		end;


	fun sko vars (FORALL(a, form)) = sko ((VAR(a))::vars) form
			| sko vars (EXISTS(a, form)) = sko vars (substitute (FUNC("skolem_" ^ a, vars)) a form)
			| sko vars form = (form, vars);

	fun addQuantifiers [] form = form
		| addQuantifiers ((VAR(x))::xs) form = addQuantifiers xs (FORALL(x, form));

	fun makeSCNF form = 
		let val (skolemized, vars) = sko [] (makePCNF form) in
			addQuantifiers vars skolemized
		end;


	fun zip acc l1 [] = acc
		| zip acc [] l2 = acc
		| zip acc (x::xs) (y::ys) = zip (acc @ [(x, y)]) xs ys;

	fun unzip acc1 acc2 [] = (acc1, acc2)
		| unzip acc1 acc2 ((x, y)::xs) = unzip (acc1 @ [x]) (acc2 @ [y]) xs; 

	fun occursCheck (VAR(x)) (CONST(y)) = false
		| occursCheck (VAR(x)) (VAR(y)) = (x = y)
		| occursCheck (VAR(x)) (FUNC(a, tl)) =
			if a = x then true
			else foldl (or) (false) (map (occursCheck (VAR(x))) tl);

	fun findDisagreement (FUNC(x, []), FUNC(y, [])) = (CONST("DONE"), CONST("DONE"))
		| findDisagreement (FUNC(x, (hd1::tl1)), FUNC(y, (hd2::tl2))) =
			if  x <> y then (CONST("NULL"), CONST("NULL"))
			else 
				let val disagreement = findDisagreement (hd1, hd2) in
					if disagreement = (CONST("DONE"), CONST("DONE")) then findDisagreement (FUNC(x, tl1), FUNC(y, tl2))
					else disagreement
				end
		| findDisagreement (x, y) = if (x = y) then (CONST("DONE"), CONST("DONE")) else (x, y);

	fun fixDisagreement (CONST("DONE"), CONST("DONE")) = (CONST("DONE"), "DONE")
		| fixDisagreement (CONST(x), CONST(y)) = (CONST("NULL"), "NULL")
		| fixDisagreement (FUNC(x, tl), CONST(y)) = (CONST("NULL"), "NULL")
		| fixDisagreement (CONST(x), FUNC(y, tl)) = (CONST("NULL"), "NULL")
		| fixDisagreement (CONST(x), VAR(y)) = (CONST(x), y)
		| fixDisagreement (VAR(x), CONST(y)) = (CONST(y), x)
		| fixDisagreement (VAR(x), VAR(y)) = (VAR(x), y)
		| fixDisagreement (VAR(x), FUNC(y, tl)) =
			if (occursCheck (VAR(x)) (FUNC(y, tl)) ) then (CONST("NULL"), "NULL") else (FUNC(y, tl), x)
		| fixDisagreement (FUNC(x, tl), VAR(y)) = 
			if (occursCheck (VAR(y)) (FUNC(x, tl)) ) then (CONST("NULL"), "NULL") else (FUNC(x, tl), y);

	fun unify mgu t1 t2 =
		let 
			val (term1, term2) = findDisagreement (t1, t2);
			val (term, var_name) = fixDisagreement (term1, term2);
		in if (term, var_name) = (CONST("NULL"), "NULL") then (false, [])
		else if (term, var_name) = (CONST("DONE"), "DONE") then (true, mgu)
		else unify (mgu @ [(term, var_name)]) (substituteTerm term var_name t1) (substituteTerm term var_name t2)
		end;

	fun isUnifiableTerm t1 t2 =
		let val (chk, mgu) = unify [] t1 t2 in chk end;

	fun mergeCNFs cl1 cl2 = 
        List.concat (List.map (fn CLS(x) => List.map (fn CLS(y) => CLS(x @ y) ) cl2) cl1);

    fun makeCNF (PRED(x, tl)) = CNF([CLS([P(x, tl)])])
        | makeCNF (NOT1(PRED(x, tl))) = CNF([CLS([N(x, tl)])])
        | makeCNF (TOP1) = CNF([])
        | makeCNF (BOTTOM1) = CNF([CLS([])])
        | makeCNF (NOT1(x)) = makeCNF(negate(x))
        | makeCNF (AND1(x, y)) =
            let 
                val CNF(cl1) = makeCNF(x);
                val CNF(cl2) = makeCNF(y);
            in CNF(cl1 @ cl2)
            end
        | makeCNF (OR1(x, y)) = 
            let 
                val CNF(cl1) = makeCNF(x);
                val CNF(cl2) = makeCNF(y);
            in CNF(mergeCNFs cl1 cl2)
            end;

    fun standarizeTerm count (CONST(x)) = CONST(x)
    	| standarizeTerm count (VAR(x)) = VAR(x ^ "_" ^ (Int.toString count))
    	| standarizeTerm count (FUNC(a, tl)) = FUNC(a, (List.map (standarizeTerm count) tl));

    fun standarizePred count (P(a, tl)) = P(a, (List.map (standarizeTerm count) tl))
    	| standarizePred count (N(a, tl)) = N(a, (List.map (standarizeTerm count) tl));

    fun standarizeCLSList count acc [] = acc
    	| standarizeCLSList count acc ((CLS(x))::xs) = standarizeCLSList (count + 1) ( acc @ [CLS(List.map (standarizePred count) x)] ) xs;

    fun standarizeCNF (CNF(cl)) = CNF(standarizeCLSList 1 [] cl);

    fun formToCNF form = 
    	let val (skolemized, vars) = sko [] (makePCNF form)
			in standarizeCNF (makeCNF skolemized) 
		end;


	fun isUnifiablePred (P(x, tl1)) (P(y, tl2)) = false
		| isUnifiablePred (N(x, tl1)) (N(y, tl2)) = false
		| isUnifiablePred (P(x, tl1)) (N(y, tl2)) = isUnifiableTerm (FUNC(x, tl1)) (FUNC(y, tl2))
		| isUnifiablePred (N(x, tl1)) (P(y, tl2)) = isUnifiableTerm (FUNC(x, tl1)) (FUNC(y, tl2));

	fun unifyPred (P(x, tl1)) (P(y, tl2)) = (false, [])
		| unifyPred (N(x, tl1)) (N(y, tl2)) = (false, [])
		| unifyPred (P(x, tl1)) (N(y, tl2)) = unify [] (FUNC(x, tl1)) (FUNC(y, tl2))
		| unifyPred (N(x, tl1)) (P(y, tl2)) = unify [] (FUNC(x, tl1)) (FUNC(y, tl2))

    fun checkProgramClause (CLS(x)) = List.foldl (or) (false) (List.map (fn(x) => case x of P(y) => true | _ => false) x);

    fun checkAllProgramClauses (CNF([])) = false
    	| checkAllProgramClauses (CNF(x)) = List.foldl (or) (false) (List.map (checkProgramClause) x);

    fun checkNoProgramClauses (CNF(x)) = List.foldl (fn(x, y) => x andalso y) (true) (List.map (fn(x) => not(checkProgramClause x)) x);

    fun checkEmptyClause (CNF(x)) = List.foldl (or) (false) (List.map (fn(x) => x = CLS([])) x);

    fun splitCNF (CNF(cl)) = List.partition (checkProgramClause) cl;

    fun getCompatibleClauses literal clause_list = List.filter (fn(CLS(cls)) => (List.foldl (or) (false) (List.map (isUnifiablePred literal) cls))) clause_list;

    fun substituteU [] lit = lit
		| substituteU ((y, x)::zs) (P(a, tl)) = substituteU zs (P(a, (List.map (substituteTerm y x) tl)))
		|  substituteU ((y, x)::zs) (N(a, tl)) = substituteU zs (N(a, (List.map (substituteTerm y x) tl)));

    fun resolveLit literal (CLS(litlist)) = 
    	let val	uni_literal = List.hd (List.filter (isUnifiablePred literal) litlist);
    		val non_uni_lits = List.filter (fn(x) => not (isUnifiablePred literal x)) litlist;
    		val (chk, mgu) = unifyPred literal uni_literal 
    	in (map (substituteU mgu) non_uni_lits)
    	end;

    fun resolveClause program_clauses [] = CLS([])
    	| resolveClause program_clauses (x::xs) = 
    		let val compatible_clauses = getCompatibleClauses x program_clauses
    		in if compatible_clauses = [] then resolveClause program_clauses xs
    			else CLS(resolveLit x (List.hd compatible_clauses) @ xs)
    			end;

    fun resolveStep (CNF([])) = CNF([])
    	| resolveStep x =
    	let val (program_clauses, goal_clauses) = splitCNF x in
    			case goal_clauses of
    				[] => CNF([])
    				| (CLS(y))::ys => 
    					let val resolvent = resolveClause program_clauses y
    					in CNF((resolvent::program_clauses) @ ys)
    					end
    				end;

    fun resolution 0 cnf = CNF([])
    	| resolution count (CNF([CLS([])])) = CNF([CLS([])])
    	| resolution count cnf = 
    		if (checkEmptyClause cnf) then CNF([CLS([])])
    		else if cnf = CNF([]) orelse (checkNoProgramClauses cnf) then CNF([])
    		(*else if (checkAllProgramClauses cnf) then CNF([])*)
    		else resolution (count - 1) (resolveStep cnf);

    fun resolve form =
    	let val cnf = formToCNF form;
    		val resolved = resolution 100 cnf
    	in if resolved = CNF([CLS([])]) then false else true
    	end;

end;

open FOL;
val lit1 = P ("Q",[FUNC("f3",[FUNC("f4",[(FUNC("f5",[VAR("7")])),VAR("7")]), VAR("9")])]);
val lit2 = P ("P",[FUNC("f5",[(VAR("7"))])]);
val lit3 = P("Q",[FUNC("f5",[(VAR("7"))]), VAR("7")] );
val lit4 = N ("P",[FUNC("f5",[(VAR("23"))])]) ;
val lit5 = N ("Q",[FUNC("f5",[(VAR("17") )]), VAR("17")]);
val induction = (AND1
			(NOT1
				(PRED("p", [FUNC("+1", [FUNC("+1", [FUNC("+1", [CONST("0")])])])])), 
			AND1(
				PRED("p", [CONST("0")]), 
				FORALL("x", IMP1(
								PRED("p", [VAR("x")]),
								PRED("p", [FUNC("+1", [VAR("x")])])
								)
					)
				)
			)
		);

val not_induction = (AND1
			((PRED("p", [FUNC("+1", [FUNC("+1", [FUNC("+1", [CONST("0")])])])])), 
			AND1(
				PRED("p", [CONST("0")]), 
				FORALL("x", IMP1(
								PRED("p", [VAR("x")]),
								PRED("p", [FUNC("+1", [VAR("x")])])
								)
					)
				)
			)
		);

val cnf = formToCNF induction;
val (program_clauses, goal_clauses) = splitCNF cnf;

(*val v = FORALL ("z", (EXISTS("u", IMP1(OR1(FORALL("r", (EXISTS("p", PRED("W", [FUNC("f3", [FUNC("f4", [VAR("x"), VAR("p")]), VAR("r")])])))), PRED("P",[VAR("x")])), PRED("Q",[FUNC("f", [VAR("y"),VAR("u"),VAR("z")])])))));*)


(*signature DataType =
sig datatype Prop =  TOP | BOTTOM
                | ATOM of string
                | NOT of Prop
                | AND of Prop * Prop
                | OR of Prop * Prop
                | IMP of Prop * Prop
                | IFF of Prop * Prop
                | ITE of Prop * Prop * Prop
    
    datatype Lit = P of string
                | N of string

    datatype Clause = CLS of (Lit list)
    
    datatype Cnf = CNF of (Clause list)

	val toPrefix : Prop -> string
	val toPostfix: Prop -> string
	val isEqual  : Prop -> Prop -> bool

    val mergeCNFs: (Clause list) -> (Clause list) -> (Clause list)
    val makeCnf  : Prop -> Cnf
    val resolve  : Cnf -> bool
end;*)

(*structure DataType = 
struct datatype Prop =  TOP | BOTTOM
                | ATOM of string
                | NOT of Prop
                | AND of Prop * Prop
                | OR of Prop * Prop
                | IMP of Prop * Prop
                | IFF of Prop * Prop
                | ITE of Prop * Prop * Prop;

        datatype Lit = P of string
                | N of string

        datatype Clause = CLS of (Lit list)

        datatype Cnf = CNF of (Clause list)


	fun toPrefix (ATOM(X)) = (X)
		| toPrefix (TOP) = ("TOP")
		| toPrefix (BOTTOM) = ("BOTTOM")
		| toPrefix (NOT(X)) = ("NOT " ^ toPrefix(X))
		| toPrefix (AND(X, Y)) = ("AND, " ^ toPrefix(X) ^ ", " ^ toPrefix(Y))
		| toPrefix (OR(X, Y)) = ("OR, " ^ toPrefix(X) ^ ", " ^ toPrefix(Y))
		| toPrefix (IMP(X, Y)) = ("IMP, " ^ toPrefix(X) ^ ", " ^ toPrefix(Y))
		| toPrefix (IFF(X, Y)) = ("IFF, " ^ toPrefix(X) ^ ", " ^ toPrefix(Y))
		| toPrefix (ITE(X, Y, Z)) = ("ITE, " ^ toPrefix(X) ^ ", " ^ toPrefix(Y) ^ ", " ^ toPrefix(Z));


	fun toPostfix (ATOM(X)) = (X)
		| toPostfix (TOP) = ("TOP")
		| toPostfix (BOTTOM) = ("BOTTOM")
		| toPostfix (NOT(X)) = ("NOT " ^ toPostfix(X))
		| toPostfix (AND(X, Y)) = (toPostfix(X) ^ ", " ^ toPostfix(Y) ^ ", AND")
		| toPostfix (OR(X, Y)) = (toPostfix(X) ^ ", " ^ toPostfix(Y) ^ ", OR")
		| toPostfix (IMP(X, Y)) = (toPostfix(X) ^ ", " ^ toPostfix(Y) ^ ", IMP")
		| toPostfix (IFF(X, Y)) = (toPostfix(X) ^ ", " ^ toPostfix(Y) ^ ", IFF")
		| toPostfix (ITE(X, Y, Z)) = (toPostfix(X) ^ ", " ^ toPostfix(Y) ^ ", " ^
		toPostfix(Z) ^ ", ITE");

	
	fun isEqual t1 t2 = 
		let
          val pre1 = toPrefix(t1);
          val post1 = toPostfix(t1);
          val pre2 = toPrefix(t2);
          val post2 = toPostfix(t2);
        in (pre1 = pre2 andalso post1 = post2)
        end;


    fun propagateNeg (ATOM(X)) = NOT(ATOM(X))
        | propagateNeg (TOP) = BOTTOM
        | propagateNeg (BOTTOM) = TOP
        | propagateNeg (NOT(X)) = X
        | propagateNeg (AND(X, Y)) = OR(propagateNeg(X), propagateNeg(Y))
        | propagateNeg (OR(X, Y)) = AND(propagateNeg(X), propagateNeg(Y));
     
    fun pushNeg (NOT(X)) = propagateNeg(X)
        | pushNeg (ATOM(X)) = ATOM(X)
        | pushNeg (TOP) = TOP
        | pushNeg (BOTTOM) = BOTTOM
        | pushNeg (AND(X, Y)) = AND(pushNeg(X), pushNeg(Y))
        | pushNeg (OR(X, Y)) = OR(pushNeg(X), pushNeg(Y));

    fun removeI (ATOM(X)) = ATOM(X)
        | removeI (TOP) = TOP
        | removeI (BOTTOM) = BOTTOM
        | removeI (NOT(X)) = NOT(removeI(X))
        | removeI (AND(X, Y)) = AND(removeI(X), removeI(Y))
        | removeI (OR(X, Y)) = OR(removeI(X), removeI(Y))
        | removeI (IMP(X, Y)) = OR(propagateNeg(removeI(X)), removeI(Y))
        | removeI (IFF(X, Y)) = 
            let 
                val Xclean = removeI(X);
                val Yclean = removeI(Y);
            in AND(OR(propagateNeg(Xclean), Yclean), OR(propagateNeg(Yclean), Xclean))
            end
        | removeI (ITE(X, Y, Z)) = 
            let 
                val Xclean = removeI(X);
            in OR(AND(X, removeI(Y)), AND(propagateNeg(X), removeI(Z)))
            end;

    fun mergeCNFs cl1 cl2 = 
        List.concat (List.map (fn CLS(x) => List.map (fn CLS(y) => CLS(x @ y) ) cl2) cl1);

    fun makeCNF (ATOM(X)) = CNF([CLS([P(X)])])
        | makeCNF (NOT(ATOM(X))) = CNF([CLS([N(X)])])
        | makeCNF (TOP) = CNF([])
        | makeCNF (BOTTOM) = CNF([CLS([])])
        | makeCNF (NOT(X)) = makeCNF(propagateNeg(X))
        | makeCNF (AND(X, Y)) =
            let 
                val CNF(cl1) = makeCNF(X);
                val CNF(cl2) = makeCNF(Y);
            in CNF(cl1 @ cl2)
            end
        | makeCNF (OR(X, Y)) = 
            let 
                val CNF(cl1) = makeCNF(X);
                val CNF(cl2) = makeCNF(Y);
            in CNF(mergeCNFs cl1 cl2)
            end;

    fun makeCnf ast = 
        let
            val ast1 = removeI (ast);
            val ast2 = pushNeg (ast1);
        in makeCNF (ast2)
        end;

    
    fun removeDuplicates eqf [] = [] 
        | removeDuplicates eqf (x::xs) = x::(removeDuplicates eqf (List.filter (eqf x) xs));

    fun remDuplicateLits (CNF(cl)) = 
        let
            fun isNotEqual x y = x <> y;
            fun remDupfrmClause (CLS(X)) = CLS(removeDuplicates (isNotEqual) (X));
        in CNF(List.map remDupfrmClause cl)
        end;
    
    fun remComplements (CNF(cl)) = 
        let
            fun isComplement (N(x)) (P(y)) = (x = y)
                | isComplement (P(x)) (N(y)) = (x = y)
                | isComplement X Y = false;
            fun hasNoComplLit (CLS(litlist)) = 
                let 
                    fun complementLit litlist lit = 
                        (List.foldl (or) (false) (List.map (isComplement lit) litlist));
                in not(List.foldl (or) (false) (List.map (complementLit litlist) litlist))
                end;
        in CNF(List.filter hasNoComplLit cl)
        end;

    fun exists l x = List.exists (fn(y) => y = x) l;

    fun remSupersets (CNF(cl)) = 
        let
            fun contains l1 l2 =
                List.foldl (fn(x, y) => x andalso y) (true) (List.map (exists l1) l2);
            fun isSuperset (CLS(l1)) (CLS(l2)) = 
                ((List.length l1) > (List.length l2)) andalso (contains l1 l2);
            fun hasNoSubset lofl l1 = 
                not (List.foldl (or) (false) (List.map (isSuperset l1) lofl));
            fun isNotEqual (CLS(l1)) (CLS(l2)) =
                if (List.length l1) <> (List.length l2) then true else not(contains l1 l2);
        in CNF(removeDuplicates (isNotEqual) (List.filter (hasNoSubset cl) cl))
        end;

    fun cleanUp cnf = 
        let 
            val cnf1 = remDuplicateLits cnf;
            val cnf2 = remComplements cnf1;if
        in remSupersets cnf2
        end;


    fun isNotEqual x y = x <> y;

    fun invLit (P(X)) = N(X) | invLit (N(X)) = P(X)

    fun partition pos neg none lofl lit = 
        case lofl of
            [] => (pos, neg, none)
            | CLS(x)::xs => 
                if (exists x lit) then (partition (CLS(List.filter (isNotEqual lit) x)::pos) neg none xs lit)
                else if (exists x (invLit lit)) then (partition pos (CLS(List.filter (isNotEqual (invLit lit)) x)::neg) none xs lit)
                else (partition pos neg (CLS(x)::none) xs lit);

    fun findSplitCNF (CNF(cl)) = 
        let 
            val literals = removeDuplicates (isNotEqual) (List.concat (List.map (fn (CLS(X)) => X) cl));
            fun findSplitLit cl [] = ([],[],[])
                | findSplitLit cl (x::xs) = 
                    let
                        val (pos, neg, none) = partition [] [] [] cl x;
                    in
                        if pos = [] orelse neg = [] then (findSplitLit cl xs)
                        else (pos, neg, none)
                    end;
        in findSplitLit cl literals
        end;

    fun resolution (CNF[(CLS([]))]) = (CNF[(CLS([]))])
        | resolution cnf = 
            let 
                val (pos, neg, none) = findSplitCNF cnf;
            in CNF((mergeCNFs pos neg) @ none)
            end;

    fun resolve (CNF([])) = true
        | resolve (CNF([CLS([])])) = false
        | resolve (cnf) = 
            let 
                val cleancnf = cleanUp cnf;
                val rescnf = resolution cleancnf;
            in resolve rescnf
            end;
end;*)

            (*fun remDupLit [] = []
                | remDupLit (x::xs) = x::(remDupLit(List.filter (fn y => y <> x) xs));
            fun remDupfrmClause (CLS(X)) = CLS(remDupLit(X));*)

                (*fun removeSupersets lofl = 
                let 
                    fun removeDuplicates [] = []
                        | removeDuplicates (x::xs) = x::(removeDuplicates(List.filter (isNotEqual x) xs));
                in removeDuplicates (isNotEqual) (List.filter (hasNoSubset lofl) lofl)
                end;*)


	(*fun disagreement [] [] = (CONST("DONE"), CONST("DONE"))
		| disagreement l1 [] = (CONST("NULL"), CONST("NULL"))
		| disagreement [] l2 = (CONST("NULL"), CONST("NULL"))
		| disagreement ((CONST(x))::xs) ((CONST(y))::ys) = (CONST("NULL"), CONST("NULL"))
		| disagreement ((FUNC(x, tl1))::xs) ((CONST(y))::ys) = (CONST("NULL"), CONST("NULL"))
		| disagreement ((CONST(x))::xs) ((FUNC(y, tl2))::ys) = (CONST("NULL"), CONST("NULL"))
		| disagreement ((FUNC(x, tl1))::xs) ((FUNC(y, tl2))::ys) = 
			if x <> y then (CONST("NULL"), CONST("NULL"))
			else
				let val dis_xy = disagreement tl1 tl2 in  
					if dis_xy = (CONST("DONE"), CONST("DONE")) then disagreement xs ys
					else dis_xy
				end
		| disagreement (x::xs) (y::ys) = if x <> y then (x, y) else disagreement xs ys;


	fun unify mgu (VAR(x), VAR(y)) = (true, mgu @ [(VAR(y), x)])
		| unify mgu (VAR(x), CONST(y)) = (true, mgu @ [(CONST(y), x)])
		| unify mgu (CONST(x), VAR(y)) = (true, mgu @ [(CONST(x), y)])
		| unify mgu (VAR(x), FUNC(y, tl)) = 
			if (foldl (or) (false) (map (occursCheck VAR(x)) tl)) then (false, [])
			else (true, mgu @ [((FUNC(y, tl)), x)])
		| unify mgu (FUNC(y, tl), VAR(x)) = 
			if (foldl (or) (false) (map (occursCheck VAR(x)) tl)) then (false, [])
			else (true, mgu @ [((FUNC(y, tl)), x)])
		| unify mgu (FUNC(x, tl1), FUNC(y, tl2)) = 
			if x <> y then (false, [])
			else 
				let val disagreement_set = disagreement tl1 tl2 in
					if disagreement_set = (CONST("DONE"), CONST("DONE")) then (true, mgu)
					else if disagreement_set = (CONST("NULL"), CONST("NULL")) then (false, [])
					else let
						val (term, var) = (y,x);
						val x_sub = substituteTerm term var (FUNC(x, tl1));
						val y_sub = substituteTerm term var (FUNC(y, tl2));
					in unify ((term, var)::mgu) x_sub y_sub
					end
				end
		| unify mgu (t1, t2)= if (t1 = t2) then (true, mgu) else (false, [])
*)

(*    fun distributeOR 
    	| distributeOR (x, AND1(y, z)) = AND1((distributeOR(x, y)), (distributeOR(x, z)))
    	| distributeOR (AND1(x, y), z) = AND1(distributeOR(x, z), distributeOR(y, z))
    	| distributeOR (x, y) = OR1(x, y)*)
