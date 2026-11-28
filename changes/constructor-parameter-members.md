kind: language

A constructor parameter names the functions without `self` and the constants of its bounds as a type parameter does: under `F: Mappable`, `F.empty()` and `F.N` are the impl's for the constructor `F` stands for, and the compiler no longer rejects `F.N` with E0312. A method of an impl of a constructor trait whose receiver is a bare `self`, and a constructor trait's method whose receiver's type isn't `Self` applied, as `self: i64`, are E0338 under both implementations, and that receiver has the error type, so no E0307 or E0311 follows from it.
