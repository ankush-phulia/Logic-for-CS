signature DataType =
sig datatype Prop =  TOP | BOTTOM
                | ATOM of string
                | NOT of Prop
                | AND of Prop * Prop
                | OR of Prop * Prop
                | IMP of Prop * Prop
                | IFF of Prop * Prop
                | ITE of Prop * Prop * Prop
		
	val toPrefix : Prop -> string
	val toPostfix: Prop -> string
	val isEqual  : Prop -> Prop -> bool
end;

structure DataType = 
struct datatype Prop =  TOP | BOTTOM
                | ATOM of string
                | NOT of Prop
                | AND of Prop * Prop
                | OR of Prop * Prop
                | IMP of Prop * Prop
                | IFF of Prop * Prop
                | ITE of Prop * Prop * Prop


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
          val p1 = toPrefix(t1);
          val p2 = toPrefix(t2);
        in p1 = p2
        end

end;

