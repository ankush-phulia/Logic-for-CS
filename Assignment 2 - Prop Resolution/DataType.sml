signature DataType =
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
end;

structure DataType = 
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
                        (List.foldl (fn(x, y) => x orelse y) (false) (List.map (isComplement lit) litlist));
                in not(List.foldl (fn(x, y) => x orelse y) (false) (List.map (complementLit litlist) litlist))
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
                not (List.foldl (fn(x, y) => x orelse y) (false) (List.map (isSuperset l1) lofl));
            fun isNotEqual (CLS(l1)) (CLS(l2)) =
                if (List.length l1) <> (List.length l2) then true else not(contains l1 l2);
        in CNF(removeDuplicates (isNotEqual) (List.filter (hasNoSubset cl) cl))
        end;

    fun cleanUp cnf = 
        let 
            val cnf1 = remDuplicateLits cnf;
            val cnf2 = remComplements cnf1;
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
end;

            (*fun remDupLit [] = []
                | remDupLit (x::xs) = x::(remDupLit(List.filter (fn y => y <> x) xs));
            fun remDupfrmClause (CLS(X)) = CLS(remDupLit(X));*)

                (*fun removeSupersets lofl = 
                let 
                    fun removeDuplicates [] = []
                        | removeDuplicates (x::xs) = x::(removeDuplicates(List.filter (isNotEqual x) xs));
                in removeDuplicates (isNotEqual) (List.filter (hasNoSubset lofl) lofl)
                end;*)