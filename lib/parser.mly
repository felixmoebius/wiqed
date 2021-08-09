%token <int> INDEX
%token <string> FREE
%token <string> GLOBAL
%token LPAREN
%token RPAREN
%token LAMBDA
%token PI
%token DOT
%token COLON
%token COMMA
%token EOF
%token STAR
%token BOX
%token AXIOM
%token THEOREM
%token PROOF
%token QED
%token DONE


%start <Syntax.prog> prog

%%

prog: l = list(toplevel); EOF { l } ;

toplevel:
  | t = theorem    { t }
  | a = axiom      { a }
  ;

theorem:
  | THEOREM; n = GLOBAL; LPAREN; p = typed_parameter_list; RPAREN; COLON; e1 = expression; PROOF; e2 = expression; QED
    { let t: Syntax.theorem = {
      name = n;
      parameter_list = p;
      proposition = e1;
      proof = e2
    } in Syntax.Theorem (t) }
  ;

axiom:
  | AXIOM; n = GLOBAL; LPAREN; p = typed_parameter_list; RPAREN; COLON; e1 = expression; DONE
    { let a: Syntax.axiom = {
      name = n;
      parameter_list = p;
      proposition = e1;
    } in Syntax.Axiom (a) }
  ;

typed_parameter_list: 
  p = separated_list(COMMA, typed_parameter) { p } ;

typed_parameter:
  n = FREE; COLON; e = expression { (n, e) };

expression:
  | LAMBDA; e1 = expression; DOT; e2 = expression
    { Syntax.Lambda (e1, e2) }
  | PI; e1 = expression; DOT; e2 = expression
    { Syntax.Pi (e1, e2) }
  | a = application 
    { a }
  | n = GLOBAL; LPAREN; a = argument_list; RPAREN
    { Syntax.Instance (n, a) }
  ;

argument_list: 
  args = separated_list(COMMA, expression) { args } ;

application:
  | e = simple 
    { e }
  | e1 = application; e2 = simple
    { Syntax.Application (e1, e2) }
  ;

simple:
  | LPAREN; e = expression; RPAREN
    { e }
  | x = FREE { Syntax.Free x }
  | i = INDEX { Syntax.Index i }
  | STAR { Syntax.Star }
  | BOX { Syntax.Box }
  ;
