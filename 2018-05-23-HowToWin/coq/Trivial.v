Theorem modus_ponens
  (P Q : Prop)
  (hPQ : P -> Q)
  (hP  : P)
       : Q.
Proof.

 apply hPQ.
 apply hP.
Qed.

Print modus_ponens.

Theorem modus_tollens
  (P Q : Prop)
  (hPQ : P -> Q)
  (hnP : ~ Q)
       : ~ P.
Proof.
 unfold not in *.
 intros hP.
 apply hnP.
 apply hPQ.
 apply hP.
Qed.

Print modus_tollens.

Theorem composition
  (P Q R : Prop)
  (pq : P -> Q)
  (qr : Q -> R)
      : P -> R.
Proof.
 intros p.
 apply qr.
 apply pq.
 apply p.
Qed.

Print composition.