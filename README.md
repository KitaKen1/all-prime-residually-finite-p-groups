# Infinite Finitely Presented Residually Finite p-Groups for Every Prime

For a prime $`p`$, the torsion condition considered here is

```math
\forall g\in G_p\quad\exists a=a(g)\in\mathbb N_0,
\qquad g^{p^a}=1.
```

The existence assertion requires an infinite abstract group with this property, an ordinary finite presentation, and residual finiteness, for every prime.

> [!NOTE]
> **Theorem (Every prime).**
>
> For every prime $`p`$, there exists an infinite finitely presented residually finite abstract $`p`$-group. More precisely, let $`R(p)`$ be the finite word algebra constructed in Section 16 of the manuscript over $`\mathbb F_p`$. Then
>
> ```math
> G_p=\ker\!\left[
> \operatorname{St}_{12}(R(p))
> \longrightarrow\operatorname{St}_{12}(\mathbb F_p)
> \right]
> ```
>
> has all four properties. The same assertion holds with any fixed rank $`n\ge12`$ in place of twelve.

Here finite presentation means finitely many generators and relators in the category of abstract groups. Residual finiteness means that every nonidentity element survives in a finite group. The group may depend on $`p`$, and the exponent may depend on the element. The notation $`\operatorname{St}(R)`$ denotes the stable Steinberg group, and $`E(R)`$ its elementary matrix image.

This repository presents a proposed paper proof for formalization. A proof sketch follows; the [PDF manuscript](PDF/all-prime-residually-finite-p-groups.pdf) contains the detailed argument, including the finite algebra construction and stable separation for that same algebra. These two steps are proved in Sections 16–22 rather than assumed in the main theorem.

## Proof sketch

### 1. Construct a finite hierarchy of word rules

Fix $`c=10000`$, $`k=10`$, and $`D=2^{21}`$. For sufficiently large $`h_0`$, use levels $`h_j=h_0D^j`$, with

```math
|\Sigma_j|=2^{ch_j},\qquad q_j=2^{h_j},\qquad L_j=2q_j+1.
```

Each level has a finite alphabet and finitely many homogeneous replacements and zero declarations, all of length at most two. A canonical block encodes an upper letter as $`q_j`$ core cells, a palette containing each of $`q_j`$ colors once, and a stop.

A transaction acquires at most $`k`$ blocks, stores the proposed data and a computation certificate, and checks the certificate by reversible reading tours. A finite self-referential program checks membership in the next level's rule table. Its runtime is polynomial in the parameter; an exponentially larger tableau fits inside the core. The program checks local rules and indexed clauses without searching for certificates.

Successful verification simulates precisely an upper replacement or zero declaration. Rollback also applies to arbitrary control states, including states not reached from a clean encoding. These facts prove that encoding preserves nonzero words and that every sufficiently long nonzero word has a unique decomposition into bounded ends and internally normalizable cut intervals (Theorem 16.2).

Define $`R(p)`$ using only the finite rule table at level zero over $`\mathbb F_p`$. Iterated encodings of nonzero upper letters give nonzero classes of unbounded degrees, hence infinite dimension. Higher levels prove properties of this one finite presentation; they are not additional defining relations.

### 2. Prove matrix nilpotence in every prime characteristic

For $`d\times d`$ numerical matrices in characteristic $`p`$, complete symmetrization satisfies

```math
m>(p-1)d^2
\quad\Longrightarrow\quad
\sum_{\sigma\in S_m}X_{\sigma(1)}\cdots X_{\sigma(m)}=0.
```

Expanding in matrix units forces at least $`p`$ equal labeled arguments in every term. Their permutation multiplicity is divisible by $`p`$.

A long nonzero word contains a long run of distinct palette colors whose other fields agree. Select the complete weighted chunks inside the first eligible run and permute them. This partitions the summands into full permutation orbits, all with the same algebra image. Symmetrization cancels each orbit once the palette is large enough.

Cut normalization moves a letter test up one level as a bounded-length chunk test. A finite prefix automaton converts chunks back to letters. The dimensions $`d_j`$ grow slowly enough that

```math
\frac{q_j}{d_j^2}\longrightarrow\infty,
```

because $`2kc/(D-1)<1`$. For each fixed prime and initial test, cancellation occurs at a finite level and propagates back to level zero (Theorem 17.4).

Given a matrix over the positive ideal, weight each chunk by a central variable $`z`$. Extracting the coefficient that counts the number of matrix factors converts eventual word-length cancellation into nilpotence of that matrix. Consequently

```math
R(p)=\mathbb F_p\oplus I(p)
```

is infinite-dimensional, finitely presented, graded with finite-dimensional homogeneous parts, and has matrix-nil positive ideal (Theorem 18.1).

### 3. Prove stable separation for the constructed algebra

The cut hierarchy assigns compatible start and end phases to long nonzero word classes, modulo $`Q_d=L_0\cdots L_d`$. The phases are invariant under replacements, respect subword offsets, and satisfy

```math
\tau(w)=\sigma(w)+|w|,
\qquad \tau(u)\ne\sigma(v)\ \Longrightarrow\ uv=0.
```

The estimate

```math
p^{v_p(2^m+1)}\le C_pm
```

shows that the prime-to-$`p`$ parts $`\ell_d=Q_d/p^{v_p(Q_d)}`$ are unbounded. The phase identities remain valid modulo $`\ell_d`$.

Let $`z`$ be killed by every degree truncation of $`\operatorname{St}(R(p))`$. Its matrix image is the identity and its degree-zero reduction is trivial. Graded block substitution and removal of the wrap entry of a cyclic shift give

```math
z^{p^a}=1\quad\text{for some }a,
\qquad W_z(C_b)=1\quad\text{for all sufficiently large }b.
```

Fix the latter bound before choosing a prime-to-$`p`$ phase modulus $`\ell`$ above it. Vanishing in a sufficiently deep truncation gives a representative entirely in long roots. Exact opposite-root commutator identities and a subgroup faithful in matrices allow these roots to be relocated to their start and end phases. Different cyclic offsets commute in the Steinberg group itself, yielding

```math
W_z(C_\ell)=z^\ell=1.
```

Both identities concern the same element. Since $`\gcd(p^a,\ell)=1`$, they imply $`z=1`$. Thus the constructed algebra satisfies

```math
\bigcap_{d\ge1}\ker\!\left[
\operatorname{St}(R(p))
\longrightarrow\operatorname{St}(R(p)/I(p)_{\ge d})
\right]=\{1\}
```

(Theorem 22.2).

### 4. Pass to a finitely presented group at rank twelve

A finite presentation of the algebra gives a finite presentation of its Steinberg group in rank at least five. The proof constructs monomial roots from short generators, verifies independence of the split and intermediate coordinate, and imposes the polynomial relators (Theorem 10.1).

Matrix nilpotence makes a matrix invertible exactly when its degree-zero reduction is invertible. A presentation by matrix relations on at most five coordinates proves centrality of the matrix kernel. The integral complex of ordered frames and the central extensions of its stabilizers then give injectivity

```math
\operatorname{St}_n(R(p))\longrightarrow\operatorname{St}(R(p))
\qquad(n\ge12)
```

(Theorem 12.1).

Every degree truncation is a finite ring. Its Steinberg group is finitely generated and perfect, with a central subgroup of finite index. A coset-transfer argument proves that this group is finite (Corollary 13.3). In particular, $`\operatorname{St}_{12}(\mathbb F_p)`$ is finite, so finite-index rewriting gives an ordinary finite presentation of $`G_p`$.

### 5. Obtain all four properties in the same group

The roots $`x_{12}(a)`$, for $`a\in I(p)`$, belong to $`G_p`$ and have distinct matrix images. They prove infinitude.

For $`g\in G_p`$, its matrix image is $`I_{12}+A`$ with $`A\in M_{12}(I(p))`$. Matrix nilpotence kills a $`p`$-power of this image. Relative central torsion kills a further $`p`$-power in the stable group, and stabilization injectivity gives the identity in $`G_p`$ itself.

Finally, stable separation detects each nonidentity element in one of the finite truncated Steinberg groups. Thus $`G_p`$ is residually finite. Its separating finite images are themselves finite $`p`$-groups.

## Detailed manuscript

- [PDF manuscript](PDF/all-prime-residually-finite-p-groups.pdf)
- [Timestamp proof](PDF/all-prime-residually-finite-p-groups.pdf.ots)

## Conclusion

The proposed proof constructs, for each prime $`p`$, one abstract group that is simultaneously infinite, finitely presented, residually finite, and elementwise of finite $`p`$-power order. The finite algebra construction and stable separation are included in the proof, so the main existence statement has no additional conjectural hypotheses. No uniform exponent over all elements is asserted.
