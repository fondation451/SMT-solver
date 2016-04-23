%{
  open Ma_spec
  
  exception Mon_Erreur;;  
%}


%token HEADER CNF NEXT
%token <int> VAR
%token EQUAL DIFFERENT
%token EOF

%start file

%type <Ma_spec.ast_file> file

%%

file:
  |HEADER; CNF; nb_var = VAR; nb_clause = VAR; NEXT; my_clause = separated_list(NEXT, clause); EOF
    {{nbV = nb_var;
      nbC = nb_clause;
      clause_l = my_clause;
    }}
;

clause:
  |out = litteral*
    {out}
;

litteral:
  |var1 = VAR; EQUAL; var2 = VAR {Equal(var1, var2)}
  |var1 = VAR; DIFFERENT; var2 = VAR {Different(var1, var2)}
;
