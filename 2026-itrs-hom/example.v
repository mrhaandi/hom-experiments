
Parameter o : Set.
Parameter a : o.
Parameter b : o.
Parameter g : o -> o.


Definition arg1 :=
  fun (y1:o)                (* a           (4,26), ω           (8,26), a              (4,24), ω            (8,24) *)
      (y2:o -> o -> o)      (* a -> ω -> a (4,26), ω -> ω -> a (8,26), ω -> a -> ga   (4,24), ω -> ω -> ga (8,24) *)
  => y2 y1 y1.

Definition arg2 :=
  fun (y3 : o -> (o -> o -> o) -> o) (* { a -> (a -> ω -> a) -> a, a -> (ω -> a -> ga) -> ga }  *)
  => y3 (y3 a
           (fun w1   (* a (4,26), *)
                w2   (* ω (4,26), *)
            => w1))
       (fun v1 (* ω *)
            v2 (* a *)
        => g v2).


Definition solution :=
  fun (x1 : o -> (o -> o -> o) -> o)           (* a -> (a -> ω -> a) -> a   (4,26),
                                                  ω -> (ω -> ω -> a) -> a   (8,26),
                                                  a -> (ω -> a -> ga) -> ga (4,24),
                                                  ω -> (ω -> ω -> ga) -> ga (8,24) *)
      (x2 : (o -> (o -> o -> o) -> o) -> o)    (* { a -> (a -> ω -> a) -> a, a -> (ω -> a -> ga) -> ga } -> ga *)
  =>
    x2
      (fun z1 (*  a           (26), a              (24) *) 
           z2 (*  a -> ω -> a (26), ω -> a -> ga   (24) *)
       => x1 z1
            (fun s1 (* a (4,26), ω (4,24) *)
                 s2 (* ω (4,26), a (4,24) *)
             => x1 b (fun u1 (* ω, ω *)
                          u2 (* ω, ω *)
                      => z2 s1 s2))).


Compute (solution arg1 arg2). 


Definition solution' :=
  fun (x1 : o -> (o -> o -> o) -> o)           (* a -> (a -> ω -> a) -> a   (4,26),
                                                  ω -> (ω -> ω -> a) -> a   (8,26),
                                                  a -> (ω -> a -> ga) -> ga (4,24),
                                                  ω -> (ω -> ω -> ga) -> ga (8,24) *)
      (x2 : (o -> (o -> o -> o) -> o) -> o)    (* { a -> (a -> ω -> a) -> a, a -> (ω -> a -> ga) -> ga } -> ga *)
  =>
    x2
      (fun z1 (*  a           (26), a              (24) *) 
           z2 (*  a -> ω -> a (26), ω -> a -> ga   (24) *)
       => x1 z1
            (fun s1 (* a (4,26), ω (4,24) *)
                 s2 (* ω (4,26), a (4,24) *)
             => x1 b (fun u1 (* ω, ω *)
                          u2 (* ω, ω *)
                      => z2 (x1 z1 (fun s1 s2 => s1)) s2))).

Compute (solution' arg1 arg2).
