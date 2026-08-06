# The van Laarhoven Lens Representation via the (Co)end Calculus

A type-changing van Laarhoven lens has the Haskell type

```haskell
type Lens s t a b =
  forall f. Functor f =>
  (a -> f b) -> s -> f t
```

We derive its concrete representation:

```text
forall f. Functor f => (a -> f b) -> s -> f t
    ≅
s -> (a, b -> t)
```

---

## 1. Setting

Let $\mathcal{C}$ be a cartesian closed category, regarded as enriched over
itself. Write $[x,y]$ for the internal hom — this *is* the hom-object
$\mathcal{C}(x,y)$ — and $\times$ for the product. Models: $\mathbf{Set}$,
and Hask (ignoring the usual complications with bottoms).

All functors are $\mathcal{C}$-enriched. A Haskell `Functor` is exactly a
Hask-enriched endofunctor: `fmap :: (a -> b) -> (f a -> f b)` is itself an
internal function, which is precisely the enrichment.

$\int_x T(x)$ denotes the (enriched) end, an object of $\mathcal{C}$;
Haskell's `forall` is its syntax. Its points are families satisfying the
wedge condition, which for a Haskell type is the free theorem — so
parametric terms are exactly points of the end, and the lens type reads

$$
\mathrm{Lens} \;=\; \int_{F} \bigl[\,[a, Fb],\ [s, Ft]\,\bigr].
$$

**Convention of the calculus.** Every isomorphism below is natural in all of
its free variables ($a$, $b$, $s$, $t$, $x$, $F$, …), and every rule of the
calculus preserves this. Established isomorphisms may therefore be
substituted under $\int$ freely; naturality is never re-derived.

---

## 2. The calculus

The rules used below, each stated once:

**(1) Functor categories.** $[\mathcal{C},\mathcal{C}]$ is a
$\mathcal{C}$-category with hom-objects

$$
\mathrm{Nat}(F,G) = \int_x [Fx,\ Gx]
\qquad\text{(Haskell: } \verb|forall x. f x -> g x|\text{)}.
$$

**(2) Currying.** $[\,a \times y,\ z\,] \cong [\,a,\ [y,z]\,]$.

**(3) Continuity.** $\Bigl[\,w,\ \int_x T(x)\,\Bigr] \cong \int_x [\,w,\ T(x)\,]$.

**(4) Yoneda.** For any $\mathcal{C}$-category $\mathcal{A}$, object
$c \in \mathcal{A}$, and $\mathcal{C}$-functor
$K \colon \mathcal{A} \to \mathcal{C}$:

$$
\int_{y \in \mathcal{A}} [\,\mathcal{A}(c,y),\ K y\,] \cong K c.
$$

Both Yoneda steps below are instances of (4), taken in different categories:
first $\mathcal{A} = \mathcal{C}$, then $\mathcal{A} =
[\mathcal{C},\mathcal{C}]$.

(The full toolkit has more — Fubini, coYoneda, homs turning coends into ends
— none of which is needed here.)

---

## 3. The indexed store functor

$$
\mathrm{Store}_{a,b}(x) = a \times [b,x].
$$

```haskell
data Store a b x = Store a (b -> x)

instance Functor (Store a b) where
  fmap h (Store u g) = Store u (h . g)
```

(The `lens` library calls this `Context`, with the fields flipped.)

Conceptually, $\mathrm{Store}_{a,b} = \mathrm{Lan}_{b}\, a$, the left Kan
extension of $a \colon \mathbf{1} \to \mathcal{C}$ along
$b \colon \mathbf{1} \to \mathcal{C}$: the pointwise formula
$(\mathrm{Lan}_b\, a)(x) = \int^{\ast \in \mathbf{1}} [b,x] \odot a$ is a
coend of copowers, and over our cartesian self-enriched base the copower is
the product $a \times [b,x]$. This is where coends live in this story; the
derivation itself needs only ends.

---

## 4. Lemma: maps out of the store functor

$$
\begin{aligned}
\mathrm{Nat}(\mathrm{Store}_{a,b},\ F)
&= \int_x \bigl[\,a \times [b,x],\ Fx\,\bigr]
  && \text{(1), def.\ of } \mathrm{Store} \\
&\cong \int_x \bigl[\,a,\ [\,[b,x],\ Fx\,]\,\bigr]
  && \text{(2)} \\
&\cong \Bigl[\,a,\ \int_x [\,[b,x],\ Fx\,]\,\Bigr]
  && \text{(3)} \\
&\cong [\,a,\ Fb\,]
  && \text{(4) in } \mathcal{A} = \mathcal{C}
\end{aligned}
$$

In Haskell, the same chain, step for step:

```haskell
forall x. (a, b -> x) -> f x
  ≅  forall x. a -> (b -> x) -> f x
  ≅  a -> forall x. (b -> x) -> f x
  ≅  a -> f b
```

Equivalently: the Lemma is the Kan adjunction
$[\mathcal{C},\mathcal{C}](\mathrm{Lan}_b\, a,\ F) \cong [a,\ Fb]$.

As always with Yoneda, the isomorphism is "evaluate at the identity":
$k \colon a \to Fb$ corresponds to the transformation
$(u,g) \mapsto Fg\,(k\,u)$, and the inverse evaluates a transformation at
$(u, \mathrm{id}_b)$ — the Haskell value `Store u id`. These two assignments
become `toVL` and `fromVL` in Section 7.

---

## 5. Theorem

$$
\begin{aligned}
\int_F \bigl[\,[a,Fb],\ [s,Ft]\,\bigr]
&\cong \int_F \bigl[\,\mathrm{Nat}(\mathrm{Store}_{a,b},\ F),\ [s,Ft]\,\bigr]
  && \text{Lemma} \\
&\cong [\,s,\ \mathrm{Store}_{a,b}(t)\,]
  && \text{(4) in } \mathcal{A} = [\mathcal{C},\mathcal{C}],\ \ K F = [s,Ft] \\
&= [\,s,\ a \times [b,t]\,]
  && \text{def.\ of } \mathrm{Store}
\end{aligned}
$$

$$
\boxed{\;
\int_F \bigl[\,[a,Fb],\ [s,Ft]\,\bigr]
\;\cong\;
[\,s,\ a \times [b,t]\,]
\;}
$$

```text
forall f. Functor f => (a -> f b) -> s -> f t   ≅   s -> (a, b -> t)
```

The proof is two applications of Yoneda: once in $\mathcal{C}$, once in the
functor category. It is the same "double Yoneda" technique that proves
`forall f. Functor f => f a -> f b ≅ a -> b`.

**Size.** $\int_F$ ranges over the large category of all endofunctors, so
its existence is not automatic — but the calculation exhibits it as
representable, and the chains hold verbatim over any full subcategory of
endofunctors containing $\mathrm{Store}_{a,b}$ (cf. Jaskelioff–O'Connor).

---

## 6. Generality

The derivation used only the closed structure of $\mathcal{C}$ and the
copower defining $\mathrm{Store}$. Hence:

* Over any $\mathcal{V}$-category $\mathcal{C}$ tensored over a symmetric
  monoidal closed $\mathcal{V}$, put
  $\mathrm{Store}_{a,b}(x) = \mathcal{C}(b,x) \odot a$ (still
  $\mathrm{Lan}_b\, a$); both chains hold verbatim and give

  $$
  \int_F [\,\mathcal{C}(a,Fb),\ \mathcal{C}(s,Ft)\,]
  \cong
  \mathcal{C}\bigl(s,\ \mathcal{C}(b,t) \odot a\bigr).
  $$

* With $\mathcal{V} = \mathbf{Set}$ and $\mathcal{C}$ locally small with
  small coproducts, this is the classical statement — but note
  $\mathcal{C}(b,t) \odot a$ is then a coproduct of *external*-hom-many
  copies of $a$. It agrees with the familiar $s \to (a,\ b \to t)$ only when
  $\mathcal{C} = \mathbf{Set}$, where external and internal hom coincide.

* `Lens s t a b` is a Haskell *type*, not a set, so the self-enriched
  reading $\mathcal{C} = \mathcal{V} = $ Hask used above is the honest
  formalization — and it is what makes the internal hom `b -> t` appear in
  the answer.

---

## 7. The Haskell witnesses

The two directions read off from the Lemma's unit and counit:

```haskell
toVL :: Functor f => (s -> (a, b -> t)) -> (a -> f b) -> s -> f t
toVL c k s = let (u, rebuild) = c s in fmap rebuild (k u)

fromVL :: (forall f. Functor f => (a -> f b) -> s -> f t)
       -> s -> (a, b -> t)
fromVL l s = case l (\u -> Store u id) s of
               Store u rebuild -> (u, rebuild)
```

`toVL` with a getter/setter pair is the `lens` constructor,
`lens getter setter k s = fmap (setter s) (k (getter s))`. The `Store`
wrapper in `fromVL` is necessary: the bare tuple `(a, b -> x)` is not a
`Functor` in `x` without a newtype.

**Round trips.** `fromVL . toVL = id` is a two-line computation.
`toVL . fromVL = id` is exactly the wedge condition of $\int_F$ — in
Haskell, the free theorem of the type. This is where the end earns its keep:
the theorem is about the end, not the bare product $\prod_F$.

The two classic single-purpose instantiations:

```haskell
view :: (forall f. Functor f => (a -> f b) -> s -> f t) -> s -> a
view l = getConst . l Const

set  :: (forall f. Functor f => (a -> f b) -> s -> f t) -> s -> b -> t
set l s b = runIdentity (l (\_ -> Identity b) s)
```

`fromVL` computes both in one pass.

---

## 8. The monomorphic case

Setting $b = a$, $t = s$:

$$
\texttt{Lens' s a}
\;\cong\;
s \to \bigl(a,\ a \to s\bigr)
\;\cong\;
(s \to a) \times (s \to a \to s),
$$

a getter and a setter (a function into a product is a pair of functions).

The isomorphism holds for *every* term of the van Laarhoven type, lawful or
not; the lens laws (`get`–`put`, `put`–`get`, `put`–`put`) are additional
properties of the concrete pair, transported faithfully by the isomorphism
but not imposed by it.

---

## 9. Example

```haskell
temperatureFahrenheit :: Lens' Thermostat Double
temperatureFahrenheit k th = fmap (setter th) (k (getter th))
```

One formula, `fmap rebuild (k focus)`; the choice of functor picks the
interpretation:

* `Const` — extract the focus (`view`);
* `Identity` — modify and rebuild (`set`, `over`);
* `Maybe` — possibly failing update;
* `Either e` — update with errors;
* `[]` — alternative updated structures;
* `Writer w` — update with accumulated output;
* `IO` — effectful update.

That one formula serves all of them is naturality in the functor — the same
fact that makes the representation theorem true.

---

## References

* Twan van Laarhoven, *CPS based functional references* (2009) — the blog
  post introducing the representation.
* Mauro Jaskelioff and Russell O'Connor, *A Representation Theorem for
  Second-Order Functionals*, JFP 25 (2015), arXiv:1402.1699 — the rigorous
  version of this note.
* Fosco Loregian, *(Co)end Calculus*, arXiv:1501.02503 — the calculus used
  throughout.
* Mitchell Riley, *Categories of Optics*, arXiv:1809.00738 — optics in the
  enriched setting.
* Bartosz Milewski, *Category Theory for Programmers* — Yoneda, ends and
  coends, at Haskell-friendly pace.
