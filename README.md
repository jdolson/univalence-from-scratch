An Idris implementation of [*A self-contained, brief and complete formulation of Voevodsky's Univalence Axiom*](https://arxiv.org/abs/1803.0229) by Martín Escardó.

For simplicity we use Idris's built in definitions of dependent products (functions), sums (pairs), and universes.
However, we define our own identity type rather than use the built in (=) type. This isn't critical, but it makes
the code match the paper more closely (Idris's identity type is also heterogeneous which can add to the confusion).

The names of most of the variables don't agree with the paper, but the top level definitions should (where named).
