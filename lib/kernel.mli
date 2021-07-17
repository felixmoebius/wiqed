open Base

val infer : Universe.t -> Context.t -> Term.t -> (Term.t, string) Result.t
val infer_normalized : Universe.t -> Context.t -> Term.t -> (Term.t, string) Result.t
val check : Universe.t -> Context.t -> Term.t -> Term.t -> (unit, string) Result.t