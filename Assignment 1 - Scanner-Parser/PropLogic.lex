structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult= (svalue, pos) token
type lexarg = string
type arg = lexarg

val pos = ref 0
fun eof fname = Tokens.EOF(!pos, !pos) 
fun error (e, l : int, _) = TextIO.output (TextIO.stdOut, String.concat[
	"line ", (Int.toString l), ": ", e, "\n" ])

%%

%header (functor PropLogicLexFun(structure Tokens: PropLogic_TOKENS));

%arg (fname:string);

ident=[A-Za-z0-9];
ws = [\ \t];

%%

\n          => (pos := (!pos) + 1; continue());
{ws}        => (continue());
{ws}+       => (Tokens.WS(yytext, !pos, !pos));

"TRUE"{ws}*      => (Tokens.TOP(!pos, !pos));
"FALSE"{ws}*     => (Tokens.BOT(!pos, !pos));
"("{ws}*         => (Tokens.LPAR(!pos, !pos));
")"{ws}*         => (Tokens.RPAR(!pos, !pos));
"NOT"{ws}*       => (Tokens.NOT(!pos, !pos));
"AND"{ws}*       => (Tokens.AND(!pos, !pos));
"OR"{ws}*        => (Tokens.OR(!pos, !pos));
"IF"{ws}*        => (Tokens.IF(!pos, !pos));
"THEN"{ws}*      => (Tokens.THEN(!pos, !pos));
"ELSE"{ws}*      => (Tokens.ELSE(!pos, !pos));
"IFF"{ws}*       => (Tokens.IFF(!pos, !pos));
{ident}+    => (Tokens.ATO(yytext, !pos, !pos));
.           => (error("bad character "^yytext, !pos, !pos); continue());
