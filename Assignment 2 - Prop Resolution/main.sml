CM.make "sources.cm";
CM.make "$/ml-yacc-lib.cm";
use "PropLogic.lex.sml";
use "PropLogic.grm.sig";
use "PropLogic.grm.sml";
use "PropLogic.sml";
Control.Print.printDepth := 100;

open DataType;


fun output (outfile:string, inputfile: string) =
    let 
      val outstream = TextIO.openAppend (outfile)
      val AST = PropLogic.compile (inputfile)
      val PreO = toPrefix(AST)
      val PostO = toPostfix(AST)
      val cnf = makeCnf(AST)
      val satisfiable = resolve(cnf)
    in TextIO.output(outstream,  (
         "Preorder : " ^ PreO ^ "\nPostorder : " ^ PostO ^ "\nSatisfiable : " ^ (Bool.toString satisfiable) ^"\n\n"))
    end;


fun LinesToOutput (outfile:string, infile:string) = 
  let
    val instream = TextIO.openIn (infile)
    fun loop (instream, outfile) = 
      case TextIO.inputLine instream of
           SOME line => 
           (let 
             val tempstream = TextIO.openOut ("temp")
            in TextIO.output(tempstream, line); 
            TextIO.closeOut tempstream; output(outfile, "temp"); loop (instream, outfile)
            end)
         | NONE => 
             (let
               val tempstream = TextIO.openOut ("temp")
              in TextIO.output(tempstream, " "); TextIO.closeIn instream
              end)
  in loop (instream, outfile) before TextIO.closeIn instream
  end


val args = CommandLine.arguments();
val infile = (hd args);
val outfile = hd (tl args);

val done = LinesToOutput (outfile, infile);

