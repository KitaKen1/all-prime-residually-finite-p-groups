"""Build the citation-free proof manuscript delivered in githubPDF/PDF."""
from pathlib import Path
from reportlab.platypus import SimpleDocTemplate, Paragraph, PageBreak, Spacer
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.colors import black

ROOT=Path(__file__).resolve().parent
DEST=ROOT/'githubPDF/PDF/all-prime-residually-finite-p-groups.pdf'
DEST.parent.mkdir(parents=True,exist_ok=True)
FD=Path('/System/Library/Fonts/Supplemental')
for name,file in [('Roman','Times New Roman.ttf'),('RomanBold','Times New Roman Bold.ttf'),
                  ('RomanItalic','Times New Roman Italic.ttf'),('RomanBI','Times New Roman Bold Italic.ttf')]:
    pdfmetrics.registerFont(TTFont(name,str(FD/file)))
pdfmetrics.registerFontFamily('Roman',normal='Roman',bold='RomanBold',italic='RomanItalic',boldItalic='RomanBI')
pdfmetrics.registerFont(TTFont('Math','/System/Library/Fonts/Apple Symbols.ttf'))
ST={
 'body':ParagraphStyle('body',fontName='Roman',fontSize=11.4,leading=16.2,spaceAfter=8,alignment=TA_JUSTIFY),
 'title':ParagraphStyle('title',fontName='RomanBold',fontSize=20,leading=24,spaceAfter=22,alignment=TA_CENTER),
 'h':ParagraphStyle('h',fontName='RomanBold',fontSize=14.5,leading=18,spaceBefore=10,spaceAfter=12,keepWithNext=True),
 'sub':ParagraphStyle('sub',fontName='RomanBold',fontSize=11.4,leading=16.2,spaceBefore=5,spaceAfter=7,keepWithNext=True),
 'eq':ParagraphStyle('eq',fontName='Roman',fontSize=12,leading=22,alignment=TA_CENTER,spaceBefore=2,spaceAfter=10),
 'hyp':ParagraphStyle('hyp',fontName='Roman',fontSize=10.9,leading=15.4,spaceAfter=7,leftIndent=12),
}
story=[]
BODY_CMAP=pdfmetrics.getFont('Roman').face.charToGlyph
MATH_CMAP=pdfmetrics.getFont('Math').face.charToGlyph
def p(t,sty='body'):
    for ch in sorted(set(t)):
        if ord(ch)>127 and ord(ch) not in BODY_CMAP:
            if ord(ch) not in MATH_CMAP:raise ValueError('Missing glyph '+repr(ch))
            t=t.replace(ch,'<font name="Math">'+ch+'</font>')
    story.append(Paragraph(t,ST[sty]))
def eq(t):p(t,'eq')
def h(t):p(t,'h')
def sub(t):p(t,'sub')
def page(t):story.append(PageBreak());h(t)

p('Infinite finitely presented residually finite<br/><i>p</i>-groups for every prime','title')
h('1. Statement and conventions')
p('Throughout, <i>p</i> is a prime and F<sub>p</sub> is the field with <i>p</i> elements. All groups are abstract groups. A <i>p</i>-group means a group in which every element has finite <i>p</i>-power order; the group itself need not be finite. A finite presentation means finitely many generators and finitely many relators.')
p('A group <i>G</i> is residually finite if, for every <i>g</i> ≠ 1, there is a homomorphism from <i>G</i> to a finite group whose value at <i>g</i> is not the identity. Let')
eq('<i>R</i> = F<sub>p</sub> ⊕ <i>I</i>, &nbsp;&nbsp; <i>I</i> = ⊕<sub>r≥1</sub> <i>I</i><sub>r</sub>')
p('be a graded unital associative algebra, with <i>I</i><sub>r</sub><i>I</i><sub>s</sub> ⊆ <i>I</i><sub>r+s</sub>. Each element is a finite sum of homogeneous terms. Write')
eq('<i>I</i><sub>≥d</sub> = ⊕<sub>r≥d</sub> <i>I</i><sub>r</sub>, &nbsp;&nbsp; <i>R</i><sub>d</sub> = <i>R</i>/<i>I</i><sub>≥d</sub> &nbsp; (<i>d</i> ≥ 1).')
p('The ideal <i>I</i> is <i>matrix-nil</i> if every matrix in M<sub>r</sub>(<i>I</i>) is nilpotent, for every finite <i>r</i>. The nilpotence exponent may depend on the matrix. Steinberg groups, their stable limit, and their matrix maps are defined in Section 2.')
p('<b>Theorem 1.1 (Existence for every prime).</b> <i>For every prime p there exists an infinite finitely presented residually finite abstract p-group. More precisely, let R(p) be the finite word algebra constructed in Section 16 over F<sub>p</sub>. For every n ≥ 12 the group</i>')
eq('<i>G</i><sub>p</sub> = ker[St<sub>n</sub>(<i>R</i>(<i>p</i>)) → St<sub>n</sub>(F<sub>p</sub>)]')
p('<i>has all four properties. In particular one may take n = 12 for every prime.</i>')
p('Theorem 18.1 proves that this particular algebra is infinite-dimensional, finitely presented, graded, and matrix-nil, with finite-dimensional homogeneous parts. Theorem 22.2 proves stable separation by its degree truncations. Sections 10-14 supply the group-theoretic steps, and Section 4 assembles them. The exponent is allowed to depend on the group element.')

page('2. Steinberg groups and natural maps')
p('For a unital associative ring <i>B</i> and <i>n</i> ≥ 3, define St<sub>n</sub>(<i>B</i>) by generators x<sub>ij</sub>(<i>b</i>), for 1 ≤ <i>i</i> ≠ <i>j</i> ≤ <i>n</i> and <i>b</i> ∈ <i>B</i>, and the relations')
eq('x<sub>ij</sub>(<i>a</i>)x<sub>ij</sub>(<i>b</i>) = x<sub>ij</sub>(<i>a</i> + <i>b</i>),')
eq('[x<sub>ij</sub>(<i>a</i>), x<sub>kl</sub>(<i>b</i>)] = 1 &nbsp; if <i>j</i> ≠ <i>k</i> and <i>i</i> ≠ <i>l</i>,')
eq('[x<sub>ij</sub>(<i>a</i>), x<sub>jk</sub>(<i>b</i>)] = x<sub>ik</sub>(<i>ab</i>) &nbsp; if <i>i, j, k</i> are distinct.')
p('Here [<i>x</i>, <i>y</i>] = <i>xyx</i><sup>−1</sup><i>y</i><sup>−1</sup>. Root addition gives x<sub>ij</sub>(0) = 1 and x<sub>ij</sub>(<i>a</i>)<sup>−1</sup> = x<sub>ij</sub>(−<i>a</i>).')
p('Let E<sub>ij</sub> denote the matrix unit and let E<sub>n</sub>(<i>B</i>) be the subgroup of GL<sub>n</sub>(<i>B</i>) generated by the elementary matrices 1<sub>n</sub> + <i>b</i>E<sub>ij</sub>. Multiplication of matrix units verifies the displayed relations, so there is a surjective homomorphism')
eq('π<sub>n</sub> : St<sub>n</sub>(<i>B</i>) → E<sub>n</sub>(<i>B</i>), &nbsp; x<sub>ij</sub>(<i>b</i>) ↦ 1<sub>n</sub> + <i>b</i>E<sub>ij</sub>.')
p('A unital ring homomorphism acts on root parameters and thus induces a homomorphism on Steinberg groups. Adjoining one coordinate also gives a homomorphism St<sub>n</sub>(<i>B</i>) → St<sub>n+1</sub>(<i>B</i>). No injectivity of these maps is built into their definition.')
p('Define St(<i>B</i>) as the direct limit of these groups. The elementary matrix groups embed by adjoining identity blocks; their union is denoted E(<i>B</i>). The maps π<sub>n</sub> induce')
eq('π : St(<i>B</i>) → E(<i>B</i>), &nbsp;&nbsp; <i>J</i>(<i>B</i>) = ker π.')
p('We shall use naturality: applying a ring map and then stabilizing has the same effect as first stabilizing and then applying the ring map. This holds on every root generator and therefore on every group element.')
p('<b>Lemma 2.1.</b> <i>For every n ≥ 3, St<sub>n</sub>(B) is perfect. Also, for fixed i ≠ j, distinct root parameters define distinct group elements.</i>')
p('<b>Proof.</b> Choose <i>k</i> different from <i>i</i>, <i>j</i>. The consecutive-root relation gives')
eq('x<sub>ij</sub>(<i>a</i>) = [x<sub>ik</sub>(<i>a</i>), x<sub>kj</sub>(1)].')
p('Every generator is therefore in the commutator subgroup. If x<sub>ij</sub>(<i>a</i>) = x<sub>ij</sub>(<i>b</i>), applying π<sub>n</sub> and comparing the (<i>i</i>, <i>j</i>) entries gives <i>a</i> = <i>b</i>. □')
p('For the graded algebra in Section 1, projection to degree zero is a unital ring homomorphism <i>R</i> → F<sub>p</sub>. It supplies the reduction maps in Theorem 1.1. Moreover <i>R</i><sub>1</sub> = F<sub>p</sub>.')

page('3. Finite-index rewriting')
p('<b>Lemma 3.1.</b> <i>A subgroup of finite index in a finitely presented group is finitely presented.</i>')
p('<b>Proof.</b> Write Γ = <i>F</i>/<i>N</i>, where <i>F</i> is the free group on a finite set <i>X</i> and <i>N</i> is the normal closure of a finite set of relators ℛ. Let <i>H</i> ≤ Γ have index <i>q</i>, and let <i>F</i><sub>0</sub> be its inverse image in <i>F</i>. Then [<i>F</i> : <i>F</i><sub>0</sub>] = <i>q</i>, <i>N</i> ⊆ <i>F</i><sub>0</sub>, and <i>H</i> ≅ <i>F</i><sub>0</sub>/<i>N</i>.')
p('Make the finite coset graph whose vertices are the right cosets <i>F</i><sub>0</sub><i>f</i>. For each <i>x</i> ∈ <i>X</i>, put a directed edge labeled <i>x</i> from <i>F</i><sub>0</sub><i>f</i> to <i>F</i><sub>0</sub><i>fx</i>. Traversing an edge backwards reads <i>x</i><sup>−1</sup>. The graph is connected because <i>X</i> generates <i>F</i>. Choose a spanning tree rooted at the identity coset.')
p('For each vertex choose the word read along its tree path from the root. These words form a finite right-coset transversal <i>T</i>, containing 1. For a word <i>f</i>, denote the representative of its coset by <span>t(<i>f</i>)</span>. For <i>t</i> ∈ <i>T</i> and <i>x</i> ∈ <i>X</i>, put')
eq('<i>y</i>(<i>t</i>, <i>x</i>) = <i>tx</i> t(<i>tx</i>)<sup>−1</sup> ∈ <i>F</i><sub>0</sub>.')
p('An edge in the spanning tree gives the trivial element. Each edge outside the tree gives one generator, with its reverse giving the inverse generator. Thus there are finitely many nontrivial generators, at most <i>q</i>|<i>X</i>|.')
p('To see directly that these freely generate <i>F</i><sub>0</sub>, read a word from the root and insert the tree path to its current vertex and its inverse between consecutive letters. If the original word ends at the root, the inserted tree paths telescope and express the word as a product of the displayed generators and their inverses. Conversely, expand a product of these generators into its edge paths. A reduced nonempty word in the edges outside the tree cannot disappear by cancelling consecutive inverse edges: after all tree excursions are removed, that same reduced edge word remains. It therefore cannot label the identity element of the free group <i>F</i>. This proves freeness.')
p('As a subgroup of <i>F</i><sub>0</sub>, the group <i>N</i> is the normal closure of the finite set')
eq('{ <i>trt</i><sup>−1</sup> : <i>t</i> ∈ <i>T</i>, <i>r</i> ∈ ℛ }.')
p('Indeed, these elements lie in <i>N</i>. Conversely, each defining conjugate <i>frf</i><sup>−1</sup> for its normal closure in <i>F</i> can be written with <i>f</i> = <i>ht</i>, where <i>h</i> ∈ <i>F</i><sub>0</sub> and <i>t</i> ∈ <i>T</i>. It then equals <i>h</i>(<i>trt</i><sup>−1</sup>)<i>h</i><sup>−1</sup>. Rewrite each of the finitely many words <i>trt</i><sup>−1</sup> in the free generators above. These are finitely many relators for <i>F</i><sub>0</sub>/<i>N</i> ≅ <i>H</i>. □')

page('4. Proof of the existence theorem')
p('<b>Proof of Theorem 1.1.</b> Fix <i>p</i> and <i>n</i> ≥ 12. Take <i>R</i> = <i>R</i>(<i>p</i>) from Theorem 18.1, put Γ = St<sub>n</sub>(<i>R</i>), and let <i>G</i><sub>p</sub> be the kernel of degree-zero reduction. We prove all four properties for this same subgroup.')
sub('Finite presentation')
p('Corollary 13.3 with <i>d</i> = 1 makes St<sub>n</sub>(F<sub>p</sub>) finite. The index of <i>G</i><sub>p</sub> in Γ equals the size of the image of the reduction map and is therefore finite. Theorem 10.1 and Lemma 3.1 give a finite presentation of <i>G</i><sub>p</sub>.')
sub('Infinitude')
p('Each x<sub>12</sub>(<i>a</i>), with <i>a</i> ∈ <i>I</i>, reduces to x<sub>12</sub>(0) = 1, so belongs to <i>G</i><sub>p</sub>. Distinct values of <i>a</i> give distinct group elements by Lemma 2.1. Since <i>R</i> is infinite-dimensional over the finite field F<sub>p</sub>, its positive-degree ideal <i>I</i> is infinite. Hence <i>G</i><sub>p</sub> is infinite.')
sub('Residual finiteness')
p('Let <i>g</i> ∈ <i>G</i><sub>p</sub> be nonidentity. Theorem 12.1 makes its image in St(<i>R</i>) nonidentity. Theorem 22.2 detects it in St(<i>R</i><sub>d</sub>) for some <i>d</i>. Naturality gives the same stable image if one first maps <i>g</i> to St<sub>n</sub>(<i>R</i><sub>d</sub>). That fixed-rank image cannot be the identity. It lies in a finite group by Corollary 13.3, giving the required finite quotient image.')
sub('Elementwise p-power torsion')
p('For <i>g</i> ∈ <i>G</i><sub>p</sub>, its matrix image has the form 1<sub>n</sub> + <i>A</i>, with <i>A</i> ∈ M<sub>n</sub>(<i>I</i>). Choose <i>N</i> such that <i>A</i><sup>N</sup> = 0, and then <i>a</i> ≥ 0 such that <i>p</i><sup>a</sup> ≥ <i>N</i>. The elements 1<sub>n</sub> and <i>A</i> commute, and all intermediate binomial coefficients for a <i>p</i>-power are divisible by <i>p</i>. Thus')
eq('π<sub>n</sub>(<i>g</i><sup>pᵃ</sup>) = (1<sub>n</sub> + <i>A</i>)<sup>pᵃ</sup> = 1<sub>n</sub> + <i>A</i><sup>pᵃ</sup> = 1<sub>n</sub>.')
p('The stable image of <i>g</i><sup>pᵃ</sup> therefore lies in <i>J</i>(<i>R</i>). Its reduction to St(F<sub>p</sub>) is trivial, because <i>g</i> already belongs to the kernel of the fixed-rank reduction. By Theorem 14.1, some <i>p</i>-power <i>p</i><sup>b</sup> kills this stable element. Theorem 12.1 gives')
eq('<i>g</i><sup>pᵃ⁺ᵇ</sup> = 1 &nbsp; in <i>G</i><sub>p</sub>.')
p('Both exponents may depend on <i>g</i>. This proves the claimed torsion property and completes the proof. □')
p('<b>Corollary 4.1.</b> <i>The groups G<sub>p</sub> are separated by finite p-group images.</i>')
p('<b>Proof.</b> Theorem 1.1 supplies finite separating images, and Lemma 5.3 shows that each such image has p-power order. □')

page('5. Graded nil algebras and finite p-group images')
p('<b>Proposition 5.1.</b> <i>Let I be an infinite-dimensional positively graded associative F<sub>p</sub>-algebra with finite-dimensional homogeneous components. If every element of I is nilpotent, then 1 + I is an infinite residually finite p-group in the unitization F<sub>p</sub> ⊕ I.</i>')
p('<b>Proof.</b> The identity (1 + <i>x</i>)(1 + <i>y</i>) = 1 + (<i>x</i> + <i>y</i> + <i>xy</i>) gives closure under multiplication. If <i>x</i><sup>N</sup> = 0, the inverse of 1 + <i>x</i> is the finite series ∑<sub>j=0</sub><sup>N−1</sup>(−<i>x</i>)<sup>j</sup>. Thus 1 + <i>I</i> is a group. For <i>p</i><sup>a</sup> ≥ <i>N</i> one has (1 + <i>x</i>)<sup>pᵃ</sup> = 1.')
p('For <i>d</i> ≥ 1, the quotient <i>I</i>/<i>I</i><sub>≥d</sub> is a finite-dimensional nilpotent algebra over F<sub>p</sub>. Projection gives a homomorphism')
eq('1 + <i>I</i> → 1 + (<i>I</i>/<i>I</i><sub>≥d</sub>).')
p('The target has cardinality <i>p</i><sup>dim(I/I<sub>≥d</sub>)</sup>. If <i>x</i> ≠ 0, choose <i>d</i> above the degree of a nonzero homogeneous component of <i>x</i>. Then 1 + <i>x</i> is not killed by this homomorphism. These finite groups therefore separate all nonidentity elements. The map <i>x</i> ↦ 1 + <i>x</i> is a bijection of sets, so the group is infinite. □')
p('<b>Corollary 5.2.</b> <i>If I is matrix-nil, the same conclusion holds for 1 + M<sub>n</sub>(I), for each finite n ≥ 1. Its degree-d quotient has cardinality p<sup>n² dim(I/I<sub>≥d</sub>)</sup>.</i>')
p('<b>Proof.</b> Apply Proposition 5.1 to the graded nil algebra M<sub>n</sub>(<i>I</i>). □')
p('Neither result asserts finite generation or finite presentation of these full groups. The finite-presentation step of Theorem 1.1 is a separate assertion about a finite-index subgroup of a fixed-rank Steinberg group.')
p('<b>Lemma 5.3.</b> <i>Every finite image of a p-group has order a power of p.</i>')
p('<b>Proof.</b> Let <i>F</i> be a finite image. Every element of <i>F</i> has <i>p</i>-power order. Suppose a prime <i>q</i> divides |<i>F</i>|. Consider the tuples (<i>a</i><sub>1</sub>, …, <i>a</i><sub>q</sub>) with product 1. There are |<i>F</i>|<sup>q−1</sup> of them, a number divisible by <i>q</i>. Cyclic rotation preserves this set: moving the first factor to the end conjugates the total product. Since <i>q</i> is prime, every rotation orbit has size 1 or <i>q</i>. The number of fixed tuples is therefore divisible by <i>q</i>.')
p('Fixed tuples have the form (<i>a</i>, …, <i>a</i>) with <i>a</i><sup>q</sup> = 1. The identity gives one fixed tuple, so there is a nonidentity such <i>a</i>. It has order <i>q</i>, which is possible in a <i>p</i>-group only when <i>q</i> = <i>p</i>. All prime divisors of |<i>F</i>| are thus <i>p</i>. □')

page('6. Complete symmetrization in characteristic p')
p('<b>Lemma 6.1.</b> <i>Let K be a field of characteristic p, and let X<sub>1</sub>, …, X<sub>m</sub> ∈ M<sub>d</sub>(K). If m &gt; (p − 1)d<sup>2</sup>, then</i>')
eq('∑<sub>σ∈S<sub>m</sub></sub> <i>X</i><sub>σ(1)</sub> ··· <i>X</i><sub>σ(m)</sub> = 0.')
p('<b>Proof.</b> The expression is multilinear. Expand each argument in the <i>d</i><sup>2</sup> matrix units. In each resulting tuple, at least <i>p</i> labeled arguments are equal, since <i>m</i> &gt; (<i>p</i> − 1)<i>d</i><sup>2</sup>. Fix <i>p</i> of these labels. Relabeling them defines a free action of S<sub>p</sub> on the set of permutations of all <i>m</i> labels. Every product is constant on an orbit. Each orbit contributes <i>p</i>! copies of the same product and therefore contributes zero. Sum over the orbits, then over the multilinear expansion. □')
p('<b>Lemma 6.2 (A free packet of chunks).</b> <i>Suppose a finite collection of summands is partitioned into orbits, each orbit having contribution</i>')
eq('<i>U</i> (∑<sub>σ∈S<sub>m</sub></sub> <i>X</i><sub>σ(1)</sub> ··· <i>X</i><sub>σ(m)</sub>) <i>V</i> ⊗ <i>w</i>,')
p('<i>where the matrices have size d over a field of characteristic p, and m &gt; (p − 1)d<sup>2</sup> for each orbit. Then the total sum is zero.</i>')
p('<b>Proof.</b> Lemma 6.1 makes the contribution of every orbit zero. □')
p('A useful sufficient size bound is obtained as follows. Suppose a run of length <i>r</i> contains complete chunks of length at most <i>b</i>, with at most two additional chunks crossing the ends. If there are <i>m</i> complete chunks, then <i>r</i> ≤ <i>mb</i> + 2<i>b</i>. Hence')
eq('<i>r</i> &gt; <i>b</i>((<i>p</i> − 1)<i>d</i><sup>2</sup> + 2) &nbsp; ⇒ &nbsp; <i>m</i> &gt; (<i>p</i> − 1)<i>d</i><sup>2</sup>.')
p('This numerical bound applies only after the summands have genuinely been partitioned into full permutation orbits with a common word factor <i>w</i>. It does not imply that an arbitrary word presentation has such orbits.')
p('<b>Lemma 6.3 (Absorbing a fixed prime).</b> <i>Suppose h<sub>j</sub> = h<sub>0</sub>D<sup>j</sup>, with h<sub>0</sub> &gt; 0 and D &gt; 1, and a sequence d<sub>j</sub> ≥ 1 satisfies</i>')
eq('log<sub>2</sub>(<i>d</i><sub>j</sub><sup>2</sup>) ≤ <i>A</i> + <i>Bj</i> + θ<i>h</i><sub>j</sub>, &nbsp; θ &lt; 1.')
p('<i>For every fixed prime p and positive constant c, one eventually has 2<sup>h<sub>j</sub></sup> &gt; c((p − 1)d<sub>j</sub><sup>2</sup> + 3).</i>')
p('<b>Proof.</b> The difference <i>h</i><sub>j</sub> − log<sub>2</sub>(<i>d</i><sub>j</sub><sup>2</sup>) is at least (1 − θ)<i>h</i><sub>0</sub><i>D</i><sup>j</sup> − <i>A</i> − <i>Bj</i>, which tends to infinity. Thus 2<sup>h<sub>j</sub></sup>/<i>d</i><sub>j</sub><sup>2</sup> tends to infinity. Since <i>d</i><sub>j</sub> ≥ 1, the claimed inequality follows. □')

page('7. Recovering matrix powers from word-length sums')
p('Let <i>A</i> be a unital associative F<sub>p</sub>-algebra generated by a finite alphabet Σ, and let <i>I</i> be the span of the images of nonempty words. Assume these images form a two-sided ideal. For a word <i>v</i>, write [<i>v</i>] for its image in <i>A</i> and |<i>v</i>| for its length. Linear dependence among word images is allowed.')
p('Set <i>K</i> = F<sub>p</sub>(<i>z</i>), where <i>z</i> is a central indeterminate. A finite chunk list consists of nonempty words <i>v</i><sub>γ</sub>, indexed by a finite set ℂ, and numerical weights <i>W</i><sub>γ</sub> ∈ M<sub>d</sub>(<i>K</i>). Its length-<i>n</i> sum is')
eq('<i>C</i><sub>n</sub> = ∑ <i>W</i><sub>γ₁</sub> ··· <i>W</i><sub>γᵣ</sub> ⊗ [<i>v</i><sub>γ₁</sub> ··· <i>v</i><sub>γᵣ</sub>],')
p('where the sum runs over all sequences γ<sub>1</sub>, …, γ<sub>r</sub> with ∑ |<i>v</i><sub>γᵢ</sub>| = <i>n</i>. It is a finite sum because every chunk has positive length.')
p('<b>Proposition 7.1.</b> <i>Suppose that, for every finite matrix size and every finite chunk list over K, the sums C<sub>n</sub> vanish for all sufficiently large n. Then I is matrix-nil.</i>')
p('<b>Proof.</b> Fix <i>T</i> ∈ M<sub>d</sub>(<i>I</i>). Expand its entries into finitely many nonempty word images and collect the scalar matrix coefficients to write')
eq('<i>T</i> = ∑<sub>γ∈ℂ</sub> <i>A</i><sub>γ</sub> ⊗ [<i>v</i><sub>γ</sub>], &nbsp; <i>A</i><sub>γ</sub> ∈ M<sub>d</sub>(F<sub>p</sub>).')
p('If the list is empty then <i>T</i> = 0. Otherwise let <i>b</i> be the largest chunk length and apply the hypothesis to the weights <i>W</i><sub>γ</sub> = <i>zA</i><sub>γ</sub>. For each <i>n</i>, the corresponding sum is the image under scalar extension of the polynomial')
eq('<i>P</i><sub>n</sub>(<i>z</i>) = ∑ <i>z</i><sup>r</sup><i>A</i><sub>γ₁</sub> ··· <i>A</i><sub>γᵣ</sub> ⊗ [<i>v</i><sub>γ₁</sub> ··· <i>v</i><sub>γᵣ</sub>],')
p('with the same word-length constraint. For all <i>n</i> ≥ <i>N</i>, its image in M<sub>d</sub>(<i>K</i> ⊗ <i>A</i>) is zero. The map M<sub>d</sub>(<i>A</i>)[<i>z</i>] → M<sub>d</sub>(<i>K</i> ⊗ <i>A</i>) is injective: expand the finitely many coefficients in an F<sub>p</sub>-basis of <i>A</i>, then use injectivity of F<sub>p</sub>[<i>z</i>] → F<sub>p</sub>(<i>z</i>) for each scalar coefficient. Therefore <i>P</i><sub>n</sub>(<i>z</i>) is the zero polynomial whenever <i>n</i> ≥ <i>N</i>.')
p('Expanding <i>T</i><sup>a</sup> and grouping its products of exactly <i>a</i> chunks by total word length gives')
eq('<i>T</i><sup>a</sup> = ∑<sub>n=a</sub><sup>ab</sup> [<i>z</i><sup>a</sup>]<i>P</i><sub>n</sub>(<i>z</i>).')
p('For <i>a</i> ≥ <i>N</i>, every polynomial on the right is zero. Hence <i>T</i><sup>a</sup> = 0. The matrix size and <i>T</i> were arbitrary. □')

page('8. Prime-to-p periods and separation')
p('<b>Lemma 8.1.</b> <i>For each prime p there is a constant C<sub>p</sub> ≥ 1 such that</i>')
eq('<i>p</i><sup>v<sub>p</sub>(2ᵐ+1)</sup> ≤ <i>C</i><sub>p</sub><i>m</i> &nbsp; for all <i>m</i> ≥ 1.')
p('<b>Proof.</b> The assertion is immediate for <i>p</i> = 2. Suppose <i>p</i> is odd, and let <i>f</i> be the order of 2 in F<sub>p</sub><sup>×</sup>. If <i>f</i> is odd, then −1 is not in the cyclic subgroup generated by 2, so <i>p</i> never divides 2<sup>m</sup> + 1. Otherwise set <i>e</i> = <i>f</i>/2. The element 2<sup>e</sup> has order two and therefore equals −1 in F<sub>p</sub>. It follows that <i>p</i> divides 2<sup>m</sup> + 1 exactly when <i>m</i> = <i>et</i> with <i>t</i> odd.')
p('Put <i>c</i> = v<sub>p</sub>(2<sup>e</sup> + 1). If <i>y</i> ≡ −1 (mod <i>p</i>) and <i>u</i> is odd and coprime to <i>p</i>, the binomial expansion of (−1 + (<i>y</i> + 1))<sup>u</sup> shows v<sub>p</sub>(<i>y</i><sup>u</sup> + 1) = v<sub>p</sub>(<i>y</i> + 1): its linear term has strictly smaller valuation than all higher terms. Raising to the <i>p</i>th power increases that valuation by one. Indeed the linear term has valuation v<sub>p</sub>(<i>y</i> + 1) + 1; every other term has larger valuation, since <i>p</i> is odd. Factoring <i>t</i> into a <i>p</i>-power and a coprime odd part gives')
eq('v<sub>p</sub>(2<sup>et</sup> + 1) = <i>c</i> + v<sub>p</sub>(<i>t</i>).')
p('Consequently <i>p</i><sup>v<sub>p</sub>(2ᵐ+1)</sup> ≤ <i>p</i><sup>c</sup><i>t</i> = (<i>p</i><sup>c</sup>/<i>e</i>)<i>m</i> in the divisible cases. Taking <i>C</i><sub>p</sub> = max(1, <i>p</i><sup>c</sup>/<i>e</i>) proves the assertion in all cases. □')
p('<b>Corollary 8.2.</b> <i>Let m<sub>j</sub> be positive integers tending to infinity and put</i>')
eq('<i>L</i><sub>j</sub> = 2<sup>m<sub>j</sub></sup> + 1, &nbsp; <i>Q</i><sub>j</sub> = ∏<sub>i=0</sub><sup>j</sup><i>L</i><sub>i</sub>, &nbsp; ℓ<sub>j</sub> = <i>Q</i><sub>j</sub>/<i>p</i><sup>v<sub>p</sub>(Q<sub>j</sub>)</sup>.')
p('<i>Then gcd(ℓ<sub>j</sub>, p) = 1 and ℓ<sub>j</sub> tends to infinity.</i>')
p('<b>Proof.</b> The prime-to-<i>p</i> part of <i>L</i><sub>j</sub> divides ℓ<sub>j</sub>. By Lemma 8.1 it is at least (2<sup>m<sub>j</sub></sup> + 1)/(<i>C</i><sub>p</sub><i>m</i><sub>j</sub>), which tends to infinity. □')
p('<b>Lemma 8.3 (Reduction of phases).</b> <i>Suppose long nonzero word classes have start and end phases modulo Q, with end phase equal to start phase plus length. Suppose their phases respect subword offsets, and a nonzero product has matching middle phases. If ℓ divides Q, reducing both phases modulo ℓ preserves all these properties.</i>')
p('<b>Proof.</b> Reduction modulo ℓ is a well-defined homomorphism from ℤ/<i>Q</i>ℤ to ℤ/ℓℤ. Apply it to each phase identity. In particular, unequal middle phases after reduction exclude a nonzero product. □')

page('9. A criterion for stable separation')
p('<b>Proposition 9.1.</b> <i>Let R be a graded algebra with degree-zero part F<sub>p</sub>. Suppose that every element z killed by every degree-truncation map on St(R) satisfies z<sup>ℓ</sup> = 1 for some positive integer ℓ coprime to p. Then the truncations separate St(R).</i>')
p('<b>Proof.</b> Let <i>z</i> be killed by every map St(<i>R</i>) → St(<i>R</i><sub>d</sub>). Its matrix image involves only finitely many coordinates. Every entry of the difference between that matrix and the identity lies in <i>I</i><sub>≥d</sub> for every <i>d</i>. Since')
eq('⋂<sub>d≥1</sub> <i>I</i><sub>≥d</sub> = {0},')
p('the matrix image of <i>z</i> is the identity. Thus <i>z</i> ∈ <i>J</i>(<i>R</i>). The case <i>d</i> = 1 says that its reduction to St(F<sub>p</sub>) is trivial. Theorem 14.1 gives <i>z</i><sup>pᵃ</sup> = 1 for some <i>a</i>. By the additional hypothesis, <i>z</i><sup>ℓ</sup> = 1 with gcd(ℓ, <i>p</i>) = 1. Choose integers <i>u</i>, <i>v</i> such that <i>up</i><sup>a</sup> + <i>v</i>ℓ = 1. Powers of the same element commute, and hence')
eq('<i>z</i> = (<i>z</i><sup>pᵃ</sup>)<sup>u</sup>(<i>z</i><sup>ℓ</sup>)<sup>v</sup> = 1.')
p('The intersection of the truncation kernels is therefore trivial. □')
p('Corollary 8.2 supplies arbitrarily large integers coprime to <i>p</i>, and Lemma 8.3 allows compatible phases to be reduced to such moduli. Sections 19-22 establish the corresponding group identity <i>z</i><sup>ℓ</sup> = 1 for the same Steinberg-group element and for the algebra constructed in Section 16. The group calculation is essential: the period estimate by itself would not imply this identity.')
from proof_extensions import append_extensions
append_extensions(p, eq, h, sub, page)

page('15. Why an algebra construction is indispensable')
p('<b>Proposition 15.1.</b> <i>For every prime p there is an infinite-dimensional graded algebra R = F<sub>p</sub> ⊕ I, with finite-dimensional homogeneous components and matrix-nil I, for which St<sub>n</sub>(R) is not even finitely generated for any n ≥ 3.</i>')
p('<b>Proof.</b> Take <i>I</i> = ⊕<sub>r≥1</sub> F<sub>p</sub><i>e</i><sub>r</sub>, put <i>e</i><sub>r</sub> in degree <i>r</i>, and define every product in <i>I</i> to be zero. Its unitization is an associative graded algebra with one-dimensional positive homogeneous components. Every matrix <i>A</i> over <i>I</i> satisfies <i>A</i><sup>2</sup> = 0.')
p('Any finite set of elementary matrices over <i>R</i> uses parameters involving only finitely many basis elements <i>e</i><sub>r</sub>. Their span <i>V</i> gives a finite subalgebra F<sub>p</sub> ⊕ <i>V</i>, closed under multiplication because <i>V</i><sup>2</sup> = 0. A finite set of arbitrary elements of E<sub>n</sub>(<i>R</i>) can first be written as finitely many elementary factors, so it too belongs to GL<sub>n</sub>(F<sub>p</sub> ⊕ <i>V</i>), a finite group. Thus E<sub>n</sub>(<i>R</i>) is locally finite. It is infinite because the matrices 1 + <i>e</i><sub>r</sub>E<sub>12</sub> are distinct. An infinite locally finite group is not finitely generated. Its surjective preimage St<sub>n</sub>(<i>R</i>) cannot be finitely generated either. □')
p('This example shows why grading, infinite dimension, finite homogeneous pieces, and matrix nilpotence alone do not imply finite presentation of the group. Sections 16-18 construct an algebra with an ordinary finite presentation as well as all of these properties.')
p('Truncations always separate matrices over a graded algebra, but the group argument must also handle elements of <i>J</i>(<i>R</i>). Theorem 14.1 gives relative elements <i>p</i>-power order. Sections 19-22 use the additional structure of the constructed algebra to obtain an annihilating exponent coprime to <i>p</i> for elements killed by every truncation. Proposition 9.1 then gives separation.')

from algebra_construction import append_algebra
append_algebra(p, eq, h, sub, page)
from stable_detection import append_detection
append_detection(p, eq, h, sub, page)

page('23. Conclusion')
p('For each prime <i>p</i>, the finite word-rule construction defines an infinite-dimensional finitely presented graded algebra <i>R</i>(<i>p</i>). Reversible verification makes the hierarchy faithful on nonzero words, while cut normalization and palette symmetrization prove that every finite matrix over its positive ideal is nilpotent. Only the finite presentation at the first level defines the algebra; the higher levels are used to prove its properties.')
p('The same hierarchy gives compatible phases on long word classes with arbitrarily large periods coprime to <i>p</i>. The long-entry and relocation arguments turn those phases into the identity <i>W</i><sub>z</sub>(<i>C</i><sub>ℓ</sub>) = <i>z</i><sup>ℓ</sup> inside the stable Steinberg group. Wrap removal gives an annihilating such ℓ, and relative <i>p</i>-power torsion forces every element in all truncation kernels to be trivial. Thus the separation assertion holds for the particular algebra already constructed.')
p('Finite presentation of Steinberg groups, fixed-rank injectivity, finiteness of their truncations, and finite-index rewriting now yield the group')
eq('<i>G</i><sub>p</sub> = ker[St<sub>12</sub>(<i>R</i>(<i>p</i>)) → St<sub>12</sub>(F<sub>p</sub>)].')
p('It is infinite, finitely presented as an abstract group, residually finite, and every element has finite <i>p</i>-power order. These properties belong to this one group for each prime; neither a conjectural algebra input nor an additional separation hypothesis remains in Theorem 1.1. There is no claim of a common exponent for all elements.')

def footer(c,doc):
    c.setFont('Roman',10);c.setFillColor(black)
    c.drawCentredString(doc.pagesize[0]/2,29,str(doc.page))

doc=SimpleDocTemplate(str(DEST),pagesize=(595.28,841.89),leftMargin=53,rightMargin=53,topMargin=42,bottomMargin=52,
 title='Infinite finitely presented residually finite p-groups for every prime',
 author='',subject='A finite word algebra and stable Steinberg separation in every prime characteristic')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print(DEST)
