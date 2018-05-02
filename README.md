# Diet Coq

(To be honest it's more like Agda.)

This is an implementation of a toy dependently typed language in 
the [K framework](https://github.com/kframework/k5), following the
excellent [Simply Easy!](http://strictlypositive.org/Easy.pdf) tutorial.
Instead of using Haskell, we extend the example type-checking languages
found [here](https://github.com/kframework/k5/tree/master/k-distribution/tutorial/1_k/5_types)
with dependent function types, some new rules for normalization during
type checking, and inductive types (to define interesting things like
natural numbers and vectors; see the `tests/` directory for some examples).


## Running it

This code requires the 5th edition of the K framework with the Java
backend. To compile it:

    kompile lambda.k --backend java

To run the program `tests/vector`:

    krun tests/vector

This will give a configuration containing the types of top-level
constructs like inductive data type constructors. The `<k>` cell will
contain the type of the last expression. For example, the file 
`tests/id-id` applies the identity to the identity:

    let id = (lambda t . (lambda x . x)) : (forall t : type) t -> t in
    id (type -> type) (id type)

Which spits out a configuration with the result type: 
(Note that `$x` is a dummy variable so this is equivalent to simply 
`type -> type`.)

    <T>
      <k>
        ( forall  $x : type ) type
      </k>
      <tenv>
        .Map
      </tenv>
      <ctors>
        .Map
      </ctors>
    </T>
