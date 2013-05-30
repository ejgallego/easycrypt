module type I = { 
  fun f() : unit
  fun init () : unit 
}.

module type IF (X:I) = { 
  fun init() : unit { X.init }
}.

module F(X:I) : I = { 
   fun f() : unit = { X.f(); }
   fun init() : unit = { X.init();}
}.
