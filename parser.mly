%token <int> INDEX
%token <string> IDENTIFIER
%token LPAREN
%token RPAREN
%token LAMBDA
%token PI
%token DOT
%token EOF
%token STAR
%token BOX

%start <Term.t option> prog

%%

prog :
  | EOF            { None }
  | e = expression { Some e }
  ;

expression:
  | LAMBDA; e1 = expression; DOT; e2 = expression
    { Term.Lambda (e1, e2) }
  | PI; e1 = expression; DOT; e2 = expression
    { Term.Pi (e1, e2) }
  | a = application 
    { a }
  ;

application:
  | e = simple 
    { e }
  | e1 = application; e2 = application
    { Term.App (e1, e2) }
  ;

simple:
  | LPAREN; e = expression; RPAREN
    { e }
  | x = IDENTIFIER { Term.Free x }
  | i = INDEX { Term.Bound i }
  | STAR { Term.Star }
  | BOX { Term.Box }
  ;
