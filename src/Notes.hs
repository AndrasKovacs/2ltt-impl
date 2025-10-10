
module Notes where


{-

λ x y.
  let z = zdef
  ... ?0 x y z ...


   a b c
?0 x y z =? rhs

   x ↦ a
   y ↦ b
   z ↦ c

we have to mark the 3rd arg as a "def" dependency

let x = true in ?0 x = x
let x = true in ?0 true = true    NOT OK

λ y.
let x = true
    m = _
in unify m y


?0 y x =? y

?0 y true =? y      -- if we wanna stick to "metas are functions", then
                       local gluing messes it up!
                       Local defs must be some special kind of dependency

  the arg must be a) marked as defn dependency b) be a local def in elab scope
  then we can "invert" it
  what if
     - defn dependency but arg is not local def:
     - not defn dependency but arg is local def:











-}
