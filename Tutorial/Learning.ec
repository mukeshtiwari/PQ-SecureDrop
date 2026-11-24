require import Real Bool DBool.

type msg.
type cp.

op enc : msg -> cp. 
op dec : cp -> msg.
op dmsg : msg distr. 
op comp : cp -> bool.


module type Challenger = {
    proc encrypt (m : msg) : cp
    proc decrypt (c : cp) : msg
}.


module C : Challenger = {
    proc encrypt (m : msg) : cp = {
        return enc(m);
    }
    proc decrypt(c : cp) : msg = {
        return dec(c);
    }
}.

module type Adversary = {
    proc guess(c : cp) : bool
    proc choose() : msg 
}.

module Adv : Adversary = {
    proc guess (c : cp) : bool = {
        return comp(c);
    }
    proc choose() : msg = {
        return witness;
    }

}.


module Game(C : Challenger, Adv : Adversary) = {
    proc ind_ror() : bool = {
        var m : msg; 
        var c : cp; 
        var b, b_adv : bool; 
        b <$ {0,1};
        if (b) {
           m <@ Adv.choose();
        } else {
           m <$ dmsg ;
        }
        c <@ C.encrypt(m);
        b_adv <@ Adv.guess(c);
        return (b_adv = b);

    }
}.

lemma ind_ror_secure : phoare [Game(C, Adv).ind_ror: true ==> res] <= (1%r/2%r).
proof. admit. qed.

