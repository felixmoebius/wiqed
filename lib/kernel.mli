open Base

val infer : ?trace:bool -> Universe.t -> Context.t -> Term.t -> (Term.t, string) Result.t
val infer_normalized : ?trace:bool -> Universe.t -> Context.t -> Term.t -> (Term.t, string) Result.t
val check : ?trace:bool -> Universe.t -> Context.t -> Term.t -> Term.t -> (unit, string) Result.t