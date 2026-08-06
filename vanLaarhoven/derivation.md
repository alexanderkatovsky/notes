# Deriving the van Laarhoven Lens Representation with Ends and Coends

A type-changing van Laarhoven lens has the Haskell type

```haskell
type Lens s t a b =
  forall f. Functor f =>
  (a -> f b) -> s -> f t
```

The corresponding concrete representation is

```haskell
s -> (a, b -> t)
```

That is, for each source value of type `s`, a lens provides

1. a focused value of type `a`;
2. a rebuilding function `b -> t`.

Our goal is to derive the isomorphism

```text
forall f. Functor f => (a -> f b) -> s -> f t
    ≅
s -> (a, b -> t)
```

using the calculus of ends and coends.

**Setting.** We work in $\mathbf{Set}$; for Haskell intuition read
$\mathbf{Set}$ as `Hask`, ignoring the usual complications with bottoms and
nontermination. Working over a general category $\mathcal{C}$ would require
extra care: the store functor below must be an endofunctor for the argument
to go through, and the product $a \times \mathbf{Set}(b,x)$ needs $a$ to be a
set. So everything below is about $[\mathbf{Set},\mathbf{Set}]$, the category
of endofunctors on $\mathbf{Set}$.

---

## 1. Interpret the polymorphic type as an end

A parametrically polymorphic function

```haskell
forall f. Functor f => (a -> f b) -> s -> f t
```

is interpreted as an end over endofunctors
$F \in [\mathbf{Set},\mathbf{Set}]$:

$$
\int_{F} \mathbf{Set}\bigl(\mathbf{Set}(a,Fb),\ \mathbf{Set}(s,Ft)\bigr).
$$

An element of this end is a family of functions, one for each functor $F$,
satisfying the wedge (dinaturality) condition: the family commutes with the
action of every natural transformation $F \Rightarrow G$. This is exactly the
free theorem that parametricity guarantees for the Haskell type, so the end
is the right categorical reading of the `forall`.

Our goal is therefore to calculate this end.

> **A size remark.** $[\mathbf{Set},\mathbf{Set}]$ is not a small category, so
> an end over it need not exist a priori. The calculation below resolves this
> in the best possible way: it exhibits the end as isomorphic to an honest
> set, $\mathbf{Set}(s,\ a \times \mathbf{Set}(b,t))$. For a careful treatment
> see Jaskelioff–O'Connor (reference at the end), where this is proved as a
> representation theorem for second-order functionals.

---

## 2. Define the indexed store functor

Define the **indexed store functor** $\mathrm{Store}_{a,b} \colon
\mathbf{Set} \to \mathbf{Set}$ by

$$
\mathrm{Store}_{a,b}(x) = a \times \mathbf{Set}(b,x).
$$

In Haskell:

```haskell
data Store a b x = Store a (b -> x)

instance Functor (Store a b) where
  fmap h (Store u g) = Store u (h . g)
```

(The `lens` library calls this functor `Context`, with the fields flipped.)

Categorically,

$$
\mathrm{Store}_{a,b} = a \odot \mathbf{Set}(b,-),
$$

the **copower** of the representable functor $\mathbf{Set}(b,-)$ by the set
$a$. In $\mathbf{Set}$-valued functors the copower is computed pointwise, and
in $\mathbf{Set}$ the copower of a set is just the product:

$$
a \odot X \cong a \times X.
$$

---

## 3. Express the store functor as a coend

Treat the set $a$ as a discrete category. A functor out of a discrete
category is just an indexed family, all dinaturality conditions are vacuous,
and therefore a coend over it is simply a coproduct:

$$
\int^{u \in a} P(u) \cong \coprod_{u \in a} P(u),
\qquad
\int_{u \in a} P(u) \cong \prod_{u \in a} P(u).
$$

Applying this to the constant family $P(u) = \mathbf{Set}(b,x)$:

$$
\int^{u \in a} \mathbf{Set}(b,x)
\cong \coprod_{u \in a} \mathbf{Set}(b,x)
\cong a \times \mathbf{Set}(b,x)
= \mathrm{Store}_{a,b}(x).
$$

---

## 4. Calculate natural transformations out of the store functor

Natural transformations between functors are computed by an end:

$$
[\mathbf{Set},\mathbf{Set}]\bigl(\mathrm{Store}_{a,b},\ F\bigr)
\cong
\int_{x} \mathbf{Set}\bigl(\mathrm{Store}_{a,b}(x),\ Fx\bigr).
$$

Substitute the coend representation of the store functor:

$$
\cong
\int_{x} \mathbf{Set}\Bigl(\int^{u \in a} \mathbf{Set}(b,x),\ Fx\Bigr).
$$

The hom functor is continuous, so a coend in its contravariant argument
becomes an end outside:

$$
\mathbf{Set}\Bigl(\int^{u} P(u),\ X\Bigr)
\cong
\int_{u} \mathbf{Set}\bigl(P(u),\ X\bigr).
$$

Therefore

$$
\cong
\int_{x} \int_{u \in a}
  \mathbf{Set}\bigl(\mathbf{Set}(b,x),\ Fx\bigr).
$$

Interchange the two ends (Fubini for ends):

$$
\cong
\int_{u \in a} \int_{x}
  \mathbf{Set}\bigl(\mathbf{Set}(b,x),\ Fx\bigr).
$$

The inner end is the Yoneda lemma:

$$
\int_{x} \mathbf{Set}\bigl(\mathbf{Set}(b,x),\ Fx\bigr)
\cong Fb.
$$

An end over a discrete category is a product, and a product of $a$-many
copies of a set is a function set:

$$
\int_{u \in a} Fb
\cong \prod_{u \in a} Fb
\cong \mathbf{Set}(a, Fb).
$$

Altogether:

$$
\boxed{\;
[\mathbf{Set},\mathbf{Set}]\bigl(\mathrm{Store}_{a,b},\ F\bigr)
\cong
\mathbf{Set}(a, Fb)
\;}
$$

or, in Haskell notation,

```haskell
(forall x. Store a b x -> f x)  ≅  (a -> f b)
```

and the isomorphism is natural in $F$ (each step above is), which is what
lets us substitute it under the end in the next section.

It is worth chasing the isomorphism through explicitly, because both
directions reappear as code in Section 6:

* given $k \colon a \to Fb$, the corresponding natural transformation is

  $$
  \theta_x(u, g) = F(g)\bigl(k(u)\bigr),
  \qquad\text{in Haskell: } \; \verb|\(Store u g) -> fmap g (k u)|;
  $$

* given $\theta$, recover $k(u) = \theta_b(u, \mathrm{id}_b)$ — "evaluate at
  the identity", as in the proof of the Yoneda lemma. The element
  $(u, \mathrm{id}_b)$, i.e. `\u -> Store u id`, is the unit of the
  isomorphism.

> **Shortcut.** The same result follows in two lines without coends, by
> currying and then Yoneda:
>
> $$
> \int_x \mathbf{Set}\bigl(a \times \mathbf{Set}(b,x),\ Fx\bigr)
> \cong \int_x \mathbf{Set}\bigl(a,\ \mathbf{Set}(\mathbf{Set}(b,x), Fx)\bigr)
> \cong \mathbf{Set}\Bigl(a,\ \int_x \mathbf{Set}(\mathbf{Set}(b,x), Fx)\Bigr)
> \cong \mathbf{Set}(a, Fb),
> $$
>
> using that $\mathbf{Set}(a,-)$ preserves ends. The coend route above is the
> same computation with the copower made explicit.

---

## 5. Substitute the store functor into the van Laarhoven end

Return to

$$
\int_{F} \mathbf{Set}\bigl(\mathbf{Set}(a,Fb),\ \mathbf{Set}(s,Ft)\bigr).
$$

Using the representation from Section 4, natural in $F$:

$$
\cong
\int_{F} \mathbf{Set}\Bigl(
  [\mathbf{Set},\mathbf{Set}](\mathrm{Store}_{a,b}, F),\
  \mathbf{Set}(s,Ft)
\Bigr).
$$

Next we move $s$ outside the end. This takes two standard steps. First, for
any sets $X$, $Y$, symmetry of the product and currying give

$$
\mathbf{Set}\bigl(X,\ \mathbf{Set}(s,Y)\bigr)
\cong \mathbf{Set}(X \times s,\ Y)
\cong \mathbf{Set}(s \times X,\ Y)
\cong \mathbf{Set}\bigl(s,\ \mathbf{Set}(X,Y)\bigr).
$$

Second, the hom functor $\mathbf{Set}(s,-)$ is continuous, so it preserves
ends. Together:

$$
\cong
\mathbf{Set}\Bigl(
  s,\
  \int_{F} \mathbf{Set}\bigl(
    [\mathbf{Set},\mathbf{Set}](\mathrm{Store}_{a,b}, F),\
    Ft
  \bigr)
\Bigr).
$$

Now look at the inner end. Writing $\mathrm{Ev}_t$ for the evaluation functor

$$
\mathrm{Ev}_t \colon [\mathbf{Set},\mathbf{Set}] \to \mathbf{Set},
\qquad
\mathrm{Ev}_t(F) = Ft,
\qquad
\mathrm{Ev}_t(\alpha) = \alpha_t,
$$

the inner end is precisely the set of natural transformations

$$
\mathrm{Nat}\Bigl(
  [\mathbf{Set},\mathbf{Set}](\mathrm{Store}_{a,b},\ -),\
  \mathrm{Ev}_t
\Bigr)
$$

from a representable functor on $[\mathbf{Set},\mathbf{Set}]$ to
$\mathrm{Ev}_t$. Apply the Yoneda lemma, this time in the functor category
$[\mathbf{Set},\mathbf{Set}]$, with representing object
$\mathrm{Store}_{a,b}$:

$$
\mathrm{Nat}\Bigl(
  [\mathbf{Set},\mathbf{Set}](\mathrm{Store}_{a,b},\ -),\
  \mathrm{Ev}_t
\Bigr)
\cong
\mathrm{Ev}_t\bigl(\mathrm{Store}_{a,b}\bigr)
= \mathrm{Store}_{a,b}(t)
= a \times \mathbf{Set}(b,t).
$$

Therefore

$$
\int_{F} \mathbf{Set}\bigl(\mathbf{Set}(a,Fb),\ \mathbf{Set}(s,Ft)\bigr)
\cong
\mathbf{Set}\bigl(s,\ a \times \mathbf{Set}(b,t)\bigr),
$$

that is,

$$
\boxed{\;
\forall F.\ (a \to Fb) \to s \to Ft
\;\cong\;
s \to \bigl(a,\ b \to t\bigr)
\;}
$$

This is the van Laarhoven lens representation theorem. Note the shape of the
argument: the theorem is two applications of the Yoneda lemma — once in
$\mathbf{Set}$ (Section 4) and once in the functor category (this section).
It is the same "double Yoneda" technique that proves, for example,
`forall f. Functor f => f a -> f b ≅ a -> b`.

---

## 6. The corresponding Haskell functions

Both directions of the isomorphism fall out of the proof.

**Concrete to van Laarhoven.** Starting from

```haskell
concrete :: s -> (a, b -> t)
```

apply `concrete` to the source, then use the "given $k$, build $\theta$"
direction of Section 4:

```haskell
toVL
  :: Functor f
  => (s -> (a, b -> t))
  -> (a -> f b) -> s -> f t
toVL concrete k s =
  let (u, rebuild) = concrete s
  in  fmap rebuild (k u)
```

If the concrete representation is given as a getter and a setter,

```haskell
getter :: s -> a
setter :: s -> b -> t
```

then

```haskell
toVLFromGetterSetter
  :: Functor f
  => (s -> a)
  -> (s -> b -> t)
  -> (a -> f b) -> s -> f t
toVLFromGetterSetter getter setter k s =
  fmap (setter s) (k (getter s))
```

which is exactly the `lens` constructor from the `lens` library:

```haskell
lens getter setter k s = fmap (setter s) (k (getter s))
```

**Van Laarhoven to concrete.** Given

```haskell
vl :: forall f. Functor f => (a -> f b) -> s -> f t
```

instantiate `f` at the store functor itself and evaluate at the unit of the
Section 4 isomorphism, `\u -> Store u id :: a -> Store a b b`:

```haskell
fromVL
  :: (forall f. Functor f => (a -> f b) -> s -> f t)
  -> s -> (a, b -> t)
fromVL vl s =
  case vl (\u -> Store u id) s of
    Store u rebuild -> (u, rebuild)
```

The intermediate result `vl (\u -> Store u id) s` has type `Store a b t`,
which is the concrete representation `(a, b -> t)` up to unwrapping. Note
that the `Store` wrapper is genuinely needed here: the bare tuple type
`(a, b -> x)` is not a `Functor` in `x` (the composite of `(,) a` after
`(->) b` needs a newtype, or `Compose`, before GHC will treat it as one), so
`vl (\u -> (u, id)) s` would not typecheck.

**Getter and setter separately.** The two most familiar instantiations of
`f` recover `view` and `set` without going through `Store`:

```haskell
get :: (forall f. Functor f => (a -> f b) -> s -> f t) -> s -> a
get vl = getConst . vl Const

put :: (forall f. Functor f => (a -> f b) -> s -> f t) -> s -> b -> t
put vl s b = runIdentity (vl (\_ -> Identity b) s)
```

`fromVL` does both in a single pass over the structure.

---

## 7. Round trips: where naturality is used

The claim is an isomorphism, so both composites must be identities.

**`fromVL . toVL = id`** is a direct computation, no naturality needed:

```haskell
fromVL (toVL c) s
  = case (let (u, r) = c s in fmap r (Store u id)) of
      Store u' r' -> (u', r')
  = case (let (u, r) = c s in Store u (r . id)) of
      Store u' r' -> (u', r')
  = c s
```

**`toVL . fromVL = id`** is where the end condition earns its keep. Fix
`vl`, a functor `f`, and `k :: a -> f b`, and let
`theta :: forall x. Store a b x -> f x` be the natural transformation
corresponding to `k` under Section 4, `theta (Store u g) = fmap g (k u)`.
Dinaturality of `vl` in its functor argument — categorically the wedge
condition of the end, in Haskell the free theorem of the type — says that
post-composing the output with `theta` equals pre-composing the input with
`theta`:

```haskell
theta . vl (\u -> Store u id) s  =  vl (theta . (\u -> Store u id)) s
                                 =  vl k s
```

since `theta (Store u id) = fmap id (k u) = k u`. Unfolding the left-hand
side gives exactly `toVL (fromVL vl) k s`. So the inverse property in this
direction is not a computation but a consequence of parametricity — which is
why the `forall` (the end) is essential to the representation theorem.

---

## 8. The monomorphic lens case

For a monomorphic lens,

```haskell
type Lens' s a =
  forall f. Functor f =>
  (a -> f a) -> s -> f s
```

set $b = a$ and $t = s$. The representation theorem becomes

$$
\boxed{\;
\texttt{Lens' s a}
\;\cong\;
s \to \bigl(a,\ a \to s\bigr)
\;}
$$

Since a function into a product is a pair of functions,

$$
s \to \bigl(a \times (a \to s)\bigr)
\;\cong\;
(s \to a) \times (s \to a \to s),
$$

a monomorphic lens is exactly a getter `s -> a` together with a setter
`s -> a -> s`, packaged as a single polymorphic function.

**A caveat about laws.** The isomorphism holds for *every* function of the
van Laarhoven type, lawful or not. The lens laws — `get`–`put`, `put`–`get`,
and `put`–`put` — are additional properties of the concrete pair; the
isomorphism transports them faithfully to conditions on the polymorphic
representation, but nothing in the derivation above imposes them.

---

## 9. Example: `temperatureFahrenheit`

Suppose

```haskell
temperatureFahrenheit :: Lens' Thermostat Double
```

By the representation theorem this is equivalent to

```haskell
Thermostat -> (Double, Double -> Thermostat)
```

The first component is the Fahrenheit getter

```haskell
getter :: Thermostat -> Double
```

and the second is the rebuilding function obtained by fixing the original
thermostat:

```haskell
setter thermostat :: Double -> Thermostat
```

The van Laarhoven implementation is

```haskell
temperatureFahrenheit k thermostat =
  fmap (setter thermostat) (k (getter thermostat))
```

The sequence is:

1. extract the current Fahrenheit value;
2. apply the caller-provided functorial operation;
3. map the rebuilding function over the result.

Different choices of functor then produce different interpretations:

* `Const` extracts the focused value (`view`);
* `Identity` modifies and rebuilds (`over`, `set`);
* `Maybe` gives a possibly failing update;
* `Either e` gives an update with errors;
* `[]` gives alternative updated structures;
* `Writer w` gives an update with accumulated output;
* `IO` gives an effectful update.

All of these arise from the single formula

```haskell
fmap rebuild (k focus)
```

because the lens is natural in the choice of functor — which, as Section 7
shows, is the same fact that makes the representation theorem true.

---

## References

* Twan van Laarhoven, *CPS based functional references* (2009) — the blog
  post introducing the representation.
* Russell O'Connor, *Functor is to Lens as Applicative is to Biplate:
  Introducing Multiplate* (2011), arXiv:1103.2841.
* Mauro Jaskelioff and Russell O'Connor, *A Representation Theorem for
  Second-Order Functionals*, Journal of Functional Programming 25 (2015),
  arXiv:1402.1699 — a rigorous version of the derivation in this note.
* Bartosz Milewski, *Category Theory for Programmers*, chapters on the
  Yoneda lemma and on ends and coends; also *Profunctor Optics: The
  Categorical View*.
* Mitchell Riley, *Categories of Optics* (2018), arXiv:1809.00738.
* Fosco Loregian, *(Co)end Calculus* (2015), arXiv:1501.02503 — for the
  end/coend toolkit used throughout (continuity of hom, Fubini, Yoneda
  reduction).
