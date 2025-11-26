\documentclass[sigplan,10pt,review]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}
\setcopyright{acmlicensed}
\copyrightyear{2025}
\acmYear{2025}
\acmDOI{XXXXXXX.XXXXXXX}
\acmConference[CPP '26]{Certified Programs and Proofs}{January 12--13, 2026}{Rennes, France}
%%
%%  Uncomment \acmBooktitle if the title of the proceedings is different
%%  from ``Proceedings of ...''!
%%
%%\acmBooktitle{Woodstock '18: ACM Symposium on Neural Gaze Detection,
%%  June 03--05, 2018, Woodstock, NY}
\acmISBN{978-1-4503-XXXX-X/2018/06}

%%% Packages %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\usepackage[utf8]{inputenc}
\usepackage[UKenglish]{babel}
\usepackage{newunicodechar}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage{mathtools}
\let\Bbbk\relax
\usepackage{amsmath,amssymb,mathbbol}
\usepackage{bbold}
\usepackage[inline]{enumitem}

%% Remove the following if there are no todo items.
\setlength {\marginparwidth }{2cm}
\usepackage[obeyFinal,textsize=footnotesize]{todonotes}
\usepackage[capitalise]{cleveref}
\newcommand{\LT}[2][]{\todo[inline,author={L-T},caption={},color={pink},#1]{#2}}
\newcommand{\FNF}[2][]{\todo[inline,author={Fred},caption={},#1]{#2}}

\usepackage{microtype}
\usepackage{newunicodechar}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Macros %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\CA}{\textrm{Cubical Agda}\xspace}
\newcommand{\Agda}{\textrm{Agda}\xspace}
\newcommand{\Set}{\mathbf{Set}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%% lhs2tex %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\cons}[1]{\mathbf{#1}}
\newcommand{\iden}{\mathit}

\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as

\definecolor{addition}{RGB}{204,255,216}
\definecolor{keyword}{RGB}{204,255,216}
\definecolor{identifier}{RGB}{204,255,216}
\newcommand{\highlight}[2]{\smash{\text{\colorbox{#1}{\kern-.1em\vphantom{\vrule height 1.2ex depth 0.1ex}\smash{\ensuremath{#2}}\kern-.1em}}}}

\let\Bbbk\relax
%include agda.fmt
%format (HL(t)) = "\highlight{addition}{" t "}"
%format ≡ = "\mathop\equiv"
%format [ = "[\kern-1.5pt"
%format ]T = "\kern-1.5pt]_{\text{T}}"
%format _[_]T = "\_[\_]_{\text{T}}"
%format ]t = "\kern-1.5pt]_{\text{t}}"
%format _[_]t = "\_[\_]_{\text{t}}"
%format [idS]T = "[\mathsf{idS}]_{\text{T}}"
%format [idS]t = "[\mathsf{idS}]_{\text{t}}"
%format [∘]T = "[\circ]_{\text{T}}"
%format [∘]t = "[\circ]_{\text{t}}"

%format _,C_ = "\_,^{\mathsf{C}}\_"
%format ,C = , "^{\mathsf{C}}"

%format SC∙ = "\mathsf{SC}^{\bullet}"
%format Ctx∙ = "\mathsf{Ctx}^{\bullet}"
%format Ty∙ = "\mathsf{Ty}^{\bullet}"
%format Tm∙ = "\mathsf{Tm}^{\bullet}"
%format Sub∙ = "\mathsf{Sub}^{\bullet}"
%format tyOf∙ = "\mathsf{tyOf}^{\bullet}"

%format Γ∙ = Γ "^{\bullet}"
%format Δ∙ = Δ "^{\bullet}"
%format t∙ = t "^{\bullet}"
%format u∙ = u "^{\bullet}"
%format σ∙ = σ "^{\bullet}"
%format τ∙ = τ "^{\bullet}"
%format p∙ = p "^{\bullet}"

%format ∅∙ = ∅ "^{\bullet}"
%format _,∙_ = "\_,^{\bullet}\_"
%format ,∙ = , "^{\bullet}"
%format _[_]T∙ = "\_[\_]^{\bullet}_{\text{T}}"
%format _[_]t∙ = "\_[\_]^{\bullet}_{\text{t}}"
%format ]t∙ = "\kern-1.5pt]^{\bullet}_{\text{t}}"
%format ]T∙ = "\kern-1.5pt]^{\bullet}_{\text{T}}"
%format tyOf[]∙ = tyOf[] "^{\bullet}"
%format [idS]t∙ = [idS]t "^{\bullet}"
%format [∘]t∙ = [∘]t "^{\bullet}"
%format π₁∙ = π₁ "^{\bullet}"
%format π₂∙ = π₂ "^{\bullet}"
%format tyOfπ₂∙ = tyOfπ₂ "^{\bullet}"


%format idS∙ = idS "^{\bullet}"
%format ∘∙ = ∘ "^{\bullet}"

%format _∙P_ = "\_" ∙ "_{\mathsf{P}}\_"
%format ∙P = ∙ "_{\mathsf{P}}"


\renewcommand\Varid[1]{\mathord{\textsf{#1}}}
%\let\Conid\Varid
%\newcommand\Keyword[1]{\textsf{\textbf{#1}}}

%% end of the preamble, start of the body of the document source.


\begin{document}

%%
%% The "title" command has an optional parameter,
%% allowing the author to define a "short title" to be used in page headers.
%\title[Can Natural Model Simplify the Metatheory of Type Theory?]{Can Inspiration From Natural Models Simplify the Metatheory of Type Theory in Cubical Agda?}

\title[Can we formalise type theory intrinsically without any compromise?]{Can we formalise type theory intrinsically without any compromise? A case study in \CA}
%%
%% The "author" command and its associated commands are used to define
%% the authors and their affiliations.
%% Of note is the shared affiliation of the first two authors, and the
%% "authornote" and "authornotemark" commands
%% used to denote shared contribution to the research.
\author{Liang-Ting Chen}
\affiliation{%
  \institution{Academia Sinica}
  \city{Taipei}
  \country{Taiwan}}
\email{liangtingchen@@as.edu.tw}

\author{Fredrik Nordvall Forsberg}
\affiliation{%
  \institution{University of Strathclyde}
  \city{Glasgow}
  \country{United Kingdom}}
\email{fredrik.nordvall-forsberg@@strath.ac.uk}

\author{Tzu-Chun Tsai}
\affiliation{%
  \institution{Academia Sinica}
  \city{Taipei}
  \country{Taiwan}}
%\affiliation{%
%  \institution{University of Amsterdam}
%  \city{Amsterdam}
%  \country{Netherlands}}

%%
%% By default, the full list of authors will be used in the page
%% headers. Often, this list is too long, and will overlap
%% other information printed in the page headers. This command allows
%% the author to define a more concise list
%% of authors' names for this purpose.
%\renewcommand{\shortauthors}{Trovato et al.}

\begin{abstract}
  We present an intrinsic representation of type theory in the proof assistant \CA, inspired by Awodey’s natural models of type theory.
  The initial natural model is defined as quotient inductive-inductive-recursive types, leading us to a syntax accepted by \CA without using any transports, postulates, or custom rewrite rules.
We formalise some meta-properties such as the standard model, normalisation by evaluation for typed terms, and strictification constructions.
Since our formalisation is carried out using \CA's native support for quotient inductive types, all our constructions compute at a reasonable speed.
When we try to develop more sophisticated metatheory, however, the `transport hell' problem reappears.  Ultimately, it remains a considerable struggle to develop the metatheory of type theory using an intrinsic representation that lacks strict equations.
The effort required is about the same whether or not the notion of natural model is used.
\end{abstract}

%% The code below is generated by the tool at http://dl.acm.org/ccs.cfm.
%% Please copy and paste the code instead of the example below.
\begin{CCSXML}
<ccs2012>
   <concept>
       <concept_id>10003752.10003790.10011740</concept_id>
       <concept_desc>Theory of computation~Type theory</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
 </ccs2012>
\end{CCSXML}

\ccsdesc[500]{Theory of computation~Type theory}

\keywords{Proof Assistants, Formalisation, Cubical Agda, Quotient Inductive-Inductive-Recursive Type}
%% A "teaser" image appears between the author and affiliation
%% information and the body of the document, and typically spans the
%% page.

%\received{20 February 2007}
%\received[revised]{12 March 2009}
%\received[accepted]{5 June 2009}

\maketitle
\bibliographystyle{ACM-Reference-Format}

\section{Introduction}

\LT[inline]{Clearly articulate what has been formalised and what has not, when appropriate? Ideally finish formalisation, otherwise scale back and discuss what has been done. (R1, R3)}
\LT[inline]{TERMINATION checker? (R1, R3)}
\FNF[inline]{Work further on the idea of strictification? (R2)}
%\LT[inline]{Alternative formulation? E.g., \url{https://web.archive.org/web/20241004151846/https://lists.chalmers.se/pipermail/agda/2019/011176.html} (R2)}

% FNF (Fri 5 Sep)

Internalising the syntax and semantics of type theory in type theory is a long-standing problem which stretches the limits of the theory~\cite{Dybjer1996,Danielsson2006,Chapman2009,McBride2010,Altenkirch2016a}.
%
There are both practical and theoretical reasons to pursue this problem.
%
On the practical side, an internal representation of type theory is needed for mechanised metatheory and metaprogramming.
%
On the theoretic side, if type theory is supposed to be a general constructive foundation of mathematics, then it should in particular be able to reason about its own syntax and semantics (up to inherent limitations due to G\"odel's incompleteness theorems).
%
In dependent type theory, types can depend on terms, which means that all of contexts, types and terms need to be defined simultaneously.
%
This is one reason why formalising type theory in type theory is hard.
%

Early approaches to formalising type theory, e.g.\ McKinna and Pollack~\cite{McKinna1999}, dealt with untyped terms that were later refined by a typing relation or setoid equality, and thus had to prove a lot of congruence lemmas by hand~\cite{Danielsson2006,Chapman2009}.
%
A breakthrough was achieved by Altenkirch and Kaposi~\cite{Altenkirch2016a}, who showed that quotient inductive-inductive types (QIITs)~\cite{Altenkirch2018} can be employed to significantly simplify the internal representation of well typed terms (or, more precisely, derivations), since equality constructors can be used to represent equations such as $\beta$- and $\eta$-equality.
%
They took Dybjer's notion of a model of type theory in the form of a category with families~\cite{Dybjer1996}, and translated it into a QIIT definition.
%
In effect, this gives rise to the \emph{initial} category with families, with the elimination principles of the QIIT giving a unique morphism of categories with families to any other model.
%
This thus gives a both principled and practical way to formalise the syntax and equational theory of type theory in type theory; the feasibility of the approach was demonstrated by e.g.\ formalising normalisation by evaluation using this representation~\cite{Altenkirch2017}.

At the time of publication of Altenkirch and Kaposi~\cite{Altenkirch2016a}, the proof assistant \Agda did not allow equality constructors in data type declarations, so a workaround known as `Licata's trick'~\cite{Licata2011} was used by postulating (equality) constructors and writing down the eliminator explicitly, which meant giving up features of the proof assistant such as dependent pattern matching.
\CA, the cubical variant of \Agda~\cite{Vezzosi2021}, is now equipped with a native support for QIITs, so it is natural to ask if we can use this support to formalise the intrinsic representation of type theory without the trick or any other compromise.

In this paper, we explore this question and see what the proof assistant provides and lacks to achieve this goal.
We quickly find that their QIIT definitions break the strict positivity --- a syntactic restriction imposed by \CA to ensure consistency.
Moreover, their definition is cumbersome to work with, since the type of later constructors or even equations often only make sense because of earlier equations.
%
In an intensional type theory, such as those implemented in proof assistants, this manifests itself in transport terms across equality proofs \emph{inside} other terms, and leads to the so-called `transport hell' --- rather than just reasoning about the terms you actually want to study, you now also have to do a lot of reasoning about transports themselves and their algebraic properties.
%
It turns out that we need an alternative way of representing type theory intrinsically without any transport hell, in order to make our formalisation of type theory more lightweight and accepted by \CA.

%
The framework of categories with families is only one of several (more or less) equivalent notions of models of type theory~\cite{Hofmann1997}, and we were wondering if any of the other notions might offer any advantages.
%
Bense~\cite{Bense2024} suggested that Awodey's notion of natural model~\cite{Awodey2018} might be a good candidate.
%
Indeed, in a natural model, the indexing of terms over their types $\mathsf{Tm}_{\Gamma} : \mathsf{Ty}(\Gamma) \to \mathsf{Set}$ (as in a category with families) is replaced by a `fibred' perspective where each term instead \emph{has} a type, as picked out by a function $\mathsf{tyOf} : \mathsf{Tm}(\Gamma) \to \mathsf{Ty}(\Gamma)$.
%
Terms and types are still indexed by contexts $\Gamma$, but since most `type mismatches' arise from equations between types, not equations between contexts (indeed many formulations of type theory does not even have a notion of context equality), this should mean that many uses of transports can be avoided.

We test this hypothesis by formalising type theory in a form inspired by natural models.
%
\CA is particularly a good fit for such a project, because not only does it support QIITs, it also supports inductive-recursive types~\cite{Dybjer1999}, which are needed to simultaneously define the recursive $\mathsf{tyOf}$ function together with the inductively defined types $\mathsf{Tm}(\Gamma)$ and $\mathsf{Ty}(\Gamma)$.
%
Indeed, it could be the lack of support for inductive-recursive definitions in many proof assistants which has held back formalisation attempts based on natural models so far.

While we manage to avoid transports occurring in its own syntax, the experiment is not an outright success.
%
Indeed, we found that when developing more sophisticated metatheory, such as when defining a logical predicate model, the use of transports along equations often reappeared.
%
Strictification~\cite{Donko2022,Kaposi2025}, a recent technique for strictifying equations, cannot be applied directly because of the lack of strict proposition in the metatheory.
%
Furthermore, we found that the use of natural models is less well supported in the Cubical Agda of today, compared to approaches based purely on QIITs.
%
This is because we are more reliant on the computational behaviour of the recursively defined $\mathsf{tyOf}$ function, and this behaviour is only available in `later' clauses, which leads to the need for hacks and tricks to work around this limitation.
%
We discuss proof assistant features and their helpfulness further towards the end of the paper, after presenting our formalisation.

\paragraph{Contributions} We make the following contributions:
\begin{itemize}
\item We present an intrinsically well typed representation of the syntax of type theory, inspired by Awodey's natural models (\cref{sec:tt}).
\item We derive elimination and recursion principles for the syntax (\cref{sec:tt:elim}), and show how it can be used to construct the standard model and the term model (\cref{sec:standard-model}).
\item We discuss strictification constructions on models, and show that they also apply to our notion of natural models (\cref{sec:strictify}).
\item We develop normalisation by evaluation for substitution calculus~(\cref{sec:nbe}) as a proof of concept: our development is carried out in \CA, which has a computational implementation of QIITs and principles such as function extensionality, so the resulting normaliser computes, and can potentially be extracted as a verified program.
\item We discuss pros and cons of our approach compared to other approaches, and which proof assistant features would be helpful to make future formalisations easier (\cref{sec:discussion}).
\end{itemize}

%\LT{the idea of using natural model appears at least in 2024 \cite{Bense2024}, and it is a natural idea to formalise type theory in this way.}
\section{Setting and metatheory}
% FNF (Sun 7 Sep)

Our formalisation is carried out in \CA with a global assumption of uniqueness of identity proofs (UIP).
\LT{Should we discharge this assumption in our formalisation, eg set-truncate where needed instead? (R1, R2)}
%
We believe it should be possible to discharge this assumption in favour of explicitly set-truncating the types we define.
%
Of course, this assumption is inconsistent, since univalence is provable in \CA.
%
However, we make sure to not make any use of univalence in our development (more generally, we do not make use of the |Glue| type, which is used to prove univalence), and we are confident that this metatheory and our formalisation are actually consistent.
%
The cubical type theory XTT~\cite{Sterling2022}, which enjoys definitional UIP without univalence, justifies our assumption.
We note that a variant of \CA which is consistent with UIP has also been requested by other users~\cite{Agda-issue2019}.
By this assumption, the term \emph{set} is used interchangeably with type, since sets are exactly types satisfying UIP in homotopy type theory~\cite{UFP2013}.


\CA implements cubical type theory, and one of the important concepts therein is the interval type |I| with two distinguished endpoints |i0| and |i1|.
%
Propositional equality |x ≡ y| in a type |A| is given by \emph{paths} in |A|, i.e., by a functions |I → A|.
More generally, dependent paths |PathP P a b| are given by dependent functions |(i : I) → P i| sending |i0| to |a : P i0| and |i1| to |b : P i1|.
Note that |P : I → Type| itself is a path in the universe |Type|, hence a witness that |P i0 ≡ P i1|, which the dependent path is \emph{over}, so paths are special cases of |PathP| with |P| being a constant path.
%
The constant path |refl = λ i → a| witnesses that equality is reflexive |a ≡ a|, and paths can be lifted to type families in the sense that there is a transport operation |subst : (P : A → Type) → x ≡ y → P x → P y|.
%
See the literature on cubical type theory for details~\cite{Vezzosi2021}.
%

\CA also allows paths to appear as the target of constructors in inductive definitions.
That is, it implements higher inductive types~\cite{Lumsdaine2020}.
%
When defining a function |f : H → X| by pattern matching out of a higher inductive type, |f| also needs to be defined on the path constructors: if |e : s ≡ t| is a path from |s| to |t| in |H|, then |f e : f s ≡ f t| should be a path from |f s| to |f t| in |X|.
%
Agda's support for simultaneous definitions allows us to define quotient inductive-inductive types (QIITs)~\cite{Altenkirch2018}, where a type |A : Type| and a type family |B : A → Type| are defined inductively simultaneously.
%
Agda even allows us to define quotient inductive-inductive-recursive types (QIIRTs), where |A : Type| and |B : A → Type| are defined inductively together with a recursive function |f : A → C|.
%
We will make use of this feature to define types, terms and the |tyOf| function from terms to types simultaneously.

For the brevity of presentation, we have made arguments implicit for equality constructors, even though they are explicit in our formalisation.
%
Similarly, we are ignoring universe levels, but they are all present in the formalisation.

\section{Type theory as quotient inductive types} \label{sec:tt}

%\FNF{Discuss ``another approach is staying completely indexed and always using PathP instead of transports'' here, or in Discussion (R2)}

In this section, we will explain why Altenkirch and Kaposi's representation~\cite{Altenkirch2016a} is hard to use in practice and rejected by \CA arising from transports in its definition.
Then, we show how their representation can be transformed to a representation based on Awodey's natural models.
This representation is accepted by \CA, since it is free from transports.

%This section's aim is to exhibit that Altenkirch and Kaposi's representation, which contains the transport hells and violates the syntactic restriction imposed by \CA, can be transformed to a representation based on Awodey's natural model, which is free from transports and accepted by \CA.
%Then, we will show how other type formers can be represented in this way.
%In the reminder of this section, we will give its elimination principle and explain how these definitions are formalised in \CA.

\subsection{Type theory as the initial CwF model} \label{sec:tt:cwf}
We briefly recall the QIIT representation given by Altenkirch and Kaposi.
Each judgement therein is defined as an inductive type, each typing rule as a constructor, and each equality between types, terms, and substitutions as an \emph{equality constructor}.
The inhabitants of these types are valid derivations in type theory, because their validity is enforced by typing constraints.
The four types of judgements in type theory are represented inductive-inductively %and indexed by their context and by their types for terms
as
\begin{code}
data Ctx  : Set
data Sub  : (Γ : Ctx)  → (Δ : Ctx) → Set
data Ty   : (Γ : Ctx)  → Set
data Tm   : (Γ : Ctx)  → (A : Ty Γ) → Set
\end{code}
For example, an inhabitant of |Tm Γ A| represents a derivation for a term of type $A$ in context |Γ|.
Rules are represented by constructors of these inductive types:
\begin{code}
data _ where
  ∅      : Ctx
  _,_    : (Γ : Ctx)(A : Ty Γ) → Ctx
  _[_]T  : (A : Ty Δ)(σ : Sub Γ Δ) → Ty Γ
  _[_]t  : (t : Tm Δ A)(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  idS    : Sub Γ Γ
  _∘_    : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  _,_    : (σ : Sub Γ Δ)(t : Tm Γ (A [ σ ]T))
    → Sub Γ (Δ , A)
  [∘]T   : A [ τ ]T [ σ ]T ≡ A [ τ ∘ σ ]T
  ...
\end{code}
 The constructor |∅| represents the empty context, and |Γ , A| a context extension, while |A [ σ ]T| and |t [ σ ]t| represent substituted types and terms, respectively.
Further, |idS| is the identity substitution, |_∘_| the constructor for substitution composition, and the second |_,_| the constructor for extending a substitution |σ| with a term |t| of type |A [ σ ]T| (making use of \Agda's support for overloaded constructor names).
The equality constructor~|[∘]T| states that type substitution by |τ| followed by type substitution by |σ| is the same as a single substitution by the composition |τ ∘ σ|.

When formulating the corresponding rule for the interaction between |_∘_| and |_,_|, we encounter a type mismatch that needs to be resolved by a transport (highlighted in \highlight{addition}{\text{green}}): %, leading to the transport hell when reasoning with this equality:
\begin{code}
,∘  : (σ , t) ∘ τ ≡ (σ ∘ τ , (HL(subst (Tm Γ) [∘]T)) (t [ τ ]t))
\end{code}
The reason is that the type of |t [ τ ]t| is |A [ σ ]T [ τ ]T| rather than the required |A [ σ ∘ τ ]T|.
However, since |Tm| is an argument to |subst|, the use of transport violates a syntactic restriction of \Agda, namely its strict positivity check.
In theory, transports are allowed in QIITs~\cite{Kaposi2019}, but it is not clear to us how this syntactic restriction should be relaxed for higher inductive types supported by \CA to take into account other cubical primitives (such as |hcomp|).

In other words, transport hell is not only an obstacle for reasoning, but also breaks strict positivity in \CA when arising in inductive definitions themselves.
The situation becomes worse once additional type formers are introduced --- such as $\Pi$-types and the type |El| of elements~\cite{Altenkirch2016a} --- since each brings further instances of this problem.
%
Of course, one could bypass the strict positivity check, but doing so would undermine the general trustworthiness of formalisation.
Another possibility is to fix the syntactic restriction for HIITs, but it is unclear what conditions should be.
Therefore, we seek for an equivalent definition without transports first.

Another source of transports arises from equations over equations, but this can be avoided by using dependent paths.
For example, the fact that the identity term substitution really acts as an identity is introduced as an equality constructor |[idS]t|, defined over the highlighted equality constructor |[idS]T : A ≡ A [ idS ]T| for the identity type substitution:
\begin{code}
[idS]t : PathP (λ i → Tm Γ ((HL([idS]T i)))) t (t [ idS ]t)
\end{code}
Although equations over equations are in principle more manageable, it quickly leads us to \emph{equations over equations over yet more equations} in their elimination rules.
Hence, it is still preferable to avoid them if possible.

\subsection{The `Ford transformation' and index elimination} \label{sec:tt:terms-without-indices}

To avoid transports in the definition itself, we note that the index |A| of |Tm Γ A| often needs an explicit proof for the typing constraint --- for example, that the term |t| in the substitution |(σ , t)| has type |A [ σ ]T| --- if this does not happen to hold strictly (i.e., up to judgemental equality), so enforcing this constraint in the index of |Tm| just shoots ourselves in the foot.
Hence, we apply the `Ford transformation'~\cite{McBride1999} (`You can have any index you want, as long as it is equal to the specified one') to move the constraint on its index to its argument as an equality proof (highlighted below):
\begin{code}
_,_∶[_] : (σ : Sub Γ Δ) (t : Tm Γ B) (HL((pt : B ≡ A [ σ ]T)))
  → Sub Γ (Δ , A)
\end{code}
The constructor |,∘| which had a transport in its type becomes
\begin{code}
,∘  : ... (σ , t ∶[ pt ]) ∘ τ
          ≡ (σ ∘ τ , t [ τ ]t ∶[ (HL(cong _[ τ ]T pt ∙ [∘]T)) ])
\end{code}
where |_∙_| is the transitivity of equality.
Although transport is not needed this time, the use of |cong| and |_∙_|
still prevent the definition from being seen as strictly positive.
Similar to the Ford transformation, this problem can be overcome by asking for another equality proof, highlighted below, as an argument:
\begin{code}
,∘ : ... (HL((qt : B [ τ ]T ≡ A [ σ ∘ τ ]T)))
   → (σ , t ∶[ pt ]) ∘ τ ≡ (σ ∘ τ) , t [ τ ]t ∶[ (HL(qt)) ]
\end{code}
As we assume UIP, the additional argument is essentially unique, so this updated constructor does not require any information but only defers the proof obligation.
%This redundant argument can be removed later when defining its eliminator (\Cref{sec:tt:elim}).

Once the Ford transformation has been applied, the index |B| in |Tm Γ B| no longer plays the role of enforcing constraints.
This opens the door to a simpler design: instead of carrying the index around, we can `Ford' all |Tm| constructors uniformly and remove the index entirely.
To preserve the necessary typing information, we simultaneously introduce an auxiliary function |tyOf : Tm Γ → Ty Γ| that records it explicitly.
In the end, the constructor |,∘| becomes
\begin{code}
,∘ : (σ : Sub Δ Θ) (t : (HL(Tm Δ))) (τ : Sub Γ Δ)
   → (pt : (HL(tyOf t)) ≡ A [ σ ]T)
   → (qt : (HL(tyOf (t [ τ ]t))) ≡ A [ σ ∘ τ ]T)
   → (σ , t ∶[ pt ]) ∘ τ ≡ (σ ∘ τ) , t [ τ ]t ∶[ qt ]
\end{code}

As a side effect, this approach also removes the need for dependent paths in the definition.
Two terms can now be compared even when it is not known in advance whether their types are equal.
For instance, the equality constructor for the identity substitution becomes
\begin{code}
  [idS]t  : t ≡ t [ idS ]t
\end{code}
where the fact that |t| and |t [ idS ]t| share the same type follows from their term equality, rather than being a \emph{requirement}.

\subsection{Representing substitution calculus using QIIRT}
Building on the changes described in \Cref{sec:tt:terms-without-indices}, we now spell out our version of substitution calculus. The following types are defined simultaneously with a recursive function (changes compared to the QIIT version highlighted):
\begin{code}
data Ctx  : Set
data Sub  : (Γ : Ctx) → (Δ : Ctx) → Set
data Ty   : (Γ : Ctx) → Set
data Tm   : (HL((Γ : Ctx) → Set))
(HL(tyOf : Tm Γ → Ty Γ))
\end{code}
Similarly to the QIIT representation, constructors are introduced for rules and equalities as follows, where we highlight constructors that are different from their QIIT counterpart:
\begin{code}
data _ where
  ∅              : Ctx
  _,_            : (Γ : Ctx)(A : Ty Γ) → Ctx
  _[_]T          : (A : Ty Δ)(σ : Sub Γ Δ) → Ty Γ
  _[_]t          : (t : Tm Δ)(σ : Sub Γ Δ) → Tm Γ
  ∅              : Sub Γ ∅
  (HL(_,_∶[_]))  : (σ : Sub Γ Δ) (t : Tm Γ) (pt : tyOf t ≡ A [ σ ]T)
    → Sub Γ (Δ , A)
  idS            : Sub Γ Γ
  _∘_            : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  π₁             : Sub Γ (Δ , A) → Sub Γ Δ
  π₂             : Sub Γ (Δ , A) → Tm Γ
  idS∘_          : idS ∘ σ ≡ σ
  _∘idS          : σ ∘ idS ≡ σ
  assocS         : (γ ∘ τ) ∘ σ ≡ γ ∘ (τ ∘ σ)
  [idS]T         : A  ≡  A  [ idS ]T
  (HL([idS]t))   : t  ≡  t  [ idS ]t
  [∘]T           : A  [ τ ]T  [ σ ]T  ≡ A  [ τ ∘ σ ]T
  (HL([∘]t))     : t  [ τ ]t  [ σ ]t  ≡ t  [ τ ∘ σ ]t
  (HL(,∘))       : (σ , t ∶[ pt ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ qt ])
\end{code}
We write |wk| for the `weakening' substitution |wk = π₁ idS : Sub (Γ , A) Γ|, and |vz| for the `top variable' |vz = π₂ idS : Tm (Γ , A)|.
This works well except that we have to interleave the function clauses of |tyOf| with constructors.
For example, we need define the function clause for |π₂ σ| before the $\eta$-law for substitution:
\begin{code}
tyOf (π₂ {Γ} {Δ} {A} σ)   = A [ π₁ σ ]T
data _ where
  ηπ : σ ≡ (π₁ σ , π₂ σ ∶[ refl ])
\end{code}
Otherwise, the proof obligation |tyOf (π₂ σ) ≡ A [ π₁ σ ]T| on the right hand side of |ηπ| cannot be fulfilled by |refl|.
We proceed with other equality constructors:
\begin{code}
data _ where
  η∅   : σ ≡ ∅S
  βπ₁  : π₁ (σ , t ∶[ p ]) ≡ σ
  βπ₂  : ... (HL((q : A [ π₁ (σ , t ∶[ p ]) ]T ≡ tyOf t)))
    → π₂ (σ , t ∶[ p ]) ≡ t
\end{code}
Note that |βπ₂| has an additional derivable equality proof |(HL(q))|.
This argument is needed as the coherence condition for
\begin{code}
tyOf (βπ₂ ... q i)  = q i
\end{code}
since again using any other function while defining inductive types breaks the strict positivity check.
The remaining clauses are given as
\begin{code}
tyOf (t [ σ ]t)  = (tyOf t) [ σ ]T
tyOf ([idS]t i)  = [idS]T i
tyOf ([∘]t i)    = [∘]T i
\end{code}
This definition is accepted by \CA\footnote{At the time of writing, \CA does not support interleaved mutual definitions, but it can be equivalently defined using forward declarations.
We will discuss this idiom in \Cref{sec:tt:mutual}.}
without any warnings or errors.
Although |Tm| is only indexed by |Γ : Ctx|, the function |tyOf| ensures that every |t : Tm Γ| has a type.
Hence, |Tm| only consists of valid derivations and is still an intrinsic representation of type theory.

Replacing the index |A : Ty| of |Tm| by a function |tyOf : Tm Γ → Ty Γ| aligns with Awodey's notion of natural model~\cite{Awodey2018} where the collections of terms and types are represented as presheaves $\mathsf{Tm}, \mathsf{Ty} \colon \mathbb{C} \to \Set$ over the category of contexts $\mathbb{C}$ and connected by a natural transformation $\mathsf{Tm} \to \mathsf{Ty}$ satisfying that each substitution into a non-empty context is equivalent to a pair of substitution and a term.
That is, we have derived the intrinsic representation of type theory as a natural model using QIIRT in \CA.
This situates our family of inductive types and their algebras within a well-studied categorical models for type theory.

\subsection{\texorpdfstring{$\Pi$}{Pi}-types}

We extend our object type theory with dependent function types.
First we define the lifting of a substitution by a type as the following abbreviation:
\begin{code}
_↑_ : (σ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ σ ]T) (Δ , A)
_↑_ {Γ} σ A =  σ ∘ π₁ {Γ , A [ σ ]T} idS,
               π₂ (idS {Γ , A [ σ ]T}) ∶[ p ]
\end{code}
where |p : tyOf (π₂ idS) ≡ A [ σ ∘ π₁ idS ]T|.
We may be tempted to use |[∘]T| to define |p|, as |tyOf (π₂ (idS {Γ , A [ σ ]T}))| is equal to |A [ σ ]T [ π₁ idS ]T| by definition.
Yet, again, we must refrain ourself from doing so during the definition of the inductive types, as \CA would see this as a strict positivity problem. Instead we introduce a \emph{superfluous} equality constructor
\LT{Make our formalisation consistent with the presentation?}
\begin{code}
data _ where
  tyOfπ₂idS : tyOf (π₂ {A = A [ σ ]T} idS)
    ≡ A [ σ ∘ π₁ idS ]T
\end{code}
which can be identified with the proof derivable from |[∘]T| using UIP afterwards.
The required equality proof |p| above is then given by this constructor.

Other constructors are introduced following the `Ford transformation', with differences compared to the usual QIIT presentation highlighted:
\begin{code}
data _ where
  Π            : (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ
  (HL(app))    : (t : Tm Γ) (B : Ty (Γ , A)) (HL((pt : tyOf t ≡ Π A B)))
    → Tm (Γ , A)
  abs          : (t : Tm (Γ , A)) → Tm Γ
  Π[]          : (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
  (HL(abs[]))  : abs t [ σ ]t ≡ abs (t [ σ ↑ A ]t)
  Πβ           : app (abs t) (tyOf t) (HL(pt))  ≡ t
  Πη           : abs (app t B pt)               ≡ t

tyOf (app t B p)      = B
tyOf (abs {A = A} t)  = Π A (tyOf t)
tyOf (abs[] σ t i)    = Π[] σ (tyOf t) i
tyOf (Πβ t pt i)      = tyOf t
tyOf (Πη t pt i)      = pt (~ i)
\end{code}

Apart from the extra clauses of |tyOf|, the main change happens in the constructor |app|.
The constraint that |t| is of type |Π A B| is enforced there, but every other constructor remains as almost the same as their QIIT definition.
We have formulated application and abstraction as an isomorphism between terms of type |B| in context |Γ , A| and terms of type |Π A B| in context |Γ|, but we can also derive ordinary application:
\begin{code}
_∶[_]$$_∶[_]  : (t : Tm Γ) → tyOf t ≡ Π A B
              → (s : Tm Γ) → tyOf s ≡ A
              → Tm Γ
t ∶[ p ]$$ s ∶[ q ] = app t _ p [ idS , s ∶[ q ∙ [idS]T ] ]t
\end{code}

As an example, we can write the identity function at type |A| as |id A = abs {A = A} (π₂ idS)|, and the identity function at type |Π A (A [ wk ]T)| applied to the identity function at type |A| is represented by
\begin{code}
idid : (A : Ty Γ) → Tm Γ
idid A = id (Π A (A [ wk ])) ∶[ refl ]$$ id A ∶[ refl ]
\end{code}
and indeed using the equality constructors, we have a proof of |tyOf (idid A) ≡ Π A (A [ wk ]T)| as expected.

\subsection{The type of Booleans}

To introduce the inductive type of Booleans, we need to specialise the substitution lifting.
Let us see its constructors (with differences highlighted) and explain why a specialisation is needed.
\begin{code}
data _ where
  𝔹      : Ty Γ
  𝔹[]    : 𝔹 [ σ ]T ≡ 𝔹
  tt ff  : Tm Γ
  tt[]   : tt [ σ ]t ≡ tt
  ff[]   : ff [ σ ]t ≡ ff

tyOf tt  = 𝔹
tyOf ff  = 𝔹
tyOf (tt[] σ i)  = 𝔹[] σ i
tyOf (ff[] σ i)  = 𝔹[] σ i

data _ where
  elim𝔹  : (P : Ty (Γ , 𝔹))
    (t : Tm Γ)  (HL((pt : tyOf t ≡ P [ idS , tt ∶[ [idS]T ] ]T)))
    (u : Tm Γ)  (HL((pu : tyOf u ≡ P [ idS , ff ∶[ [idS]T ] ]T)))
    (b : Tm Γ)  (HL((pb : tyOf b ≡ 𝔹 [ idS ]))) → Tm Γ

tyOf (elim𝔹 P u t pu pt b pb) = P [ idS , b ∶[ pb ] ]T
\end{code}
The only thing missing from the above definition is the substitution rule for |elim𝔹|:
applying the substitution |σ| to `|elim𝔹 P t pt u pu b pb|' is equal to applying a lifted substitution  |σ ↑ 𝔹| to |P| and |σ| to |t|, |u|, and |b|.
However, |P [ σ ↑ 𝔹 ]T| gives us a type in the context |Δ , 𝔹 [ σ ]T| instead of |Δ , 𝔹|, so we provide a lifting with a type |Sub Γ Δ → Sub (Γ , 𝔹) (Δ , 𝔹)| and also a superfluous equality constructor |𝔹[]₂| to satisfy its proof obligation (highlighted):
\begin{code}
data _ where
  𝔹[]₂   : tyOf (π₂ {Γ , 𝔹} idS) ≡ 𝔹 [ τ ]T

_↑𝔹 : (σ : Sub Γ Δ) → Sub (Γ , 𝔹) (Δ , 𝔹)
_↑𝔹 {Γ} {Δ} σ = σ ∘ π₁ {Γ , 𝔹} idS , π₂ idS ∶[ (HL(𝔹[]₂)) ]
\end{code}

Finally, we introduce the equality constructor for the interaction between |elim𝔹| and substitution:
\begin{code}
data _ where
  elim𝔹[] : ...
    (pt₂ : tyOf (t [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , tt ∶[ [idS]T ] ]T)
    (pu₂ : tyOf (u [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , ff ∶[ [idS]T ] ]T)
    (pb₂ : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
    (q :  P [ idS , b ∶[ pb ] ]T [ σ ]T
          ≡ P [ σ ∘ wk , vz ∶[ 𝔹[]₂ ] ]T [ idS , b [ σ ]t ∶[ pb₂ ] ]T)
    → (elim𝔹  P t pt u pu b pb) [ σ ]t
          ≡ elim𝔹 (P [ σ ↑𝔹 ]T)  (t [ σ ]t) pt₂ (u [ σ ]t) pu₂
                                 (b [ σ ]t) pb₂

tyOf (elim𝔹[] P u t pu pt b pb pt₂ pu₂ pb₂ q i) = q i
\end{code}
Note again that we also defer the coherence proof of |tyOf| for |elim𝔹[]| by introducing another argument |q| in |elim𝔹| which can be removed when defining its elimination rule.

\subsection{A Tarski universe} \label{sec:tt:univ}
Using the same idiom described previously, a Tarski universe of types is introduced to our type theory in the same vein.
First we need |U : Ty Γ| as the type of codes, and a type family |El| of elements for a given code (differences compared to the usual presentation highlighted):
\begin{code}
data _ where
  U     : Ty Γ
  U[]   : U [ σ ]T ≡ U
  El    : (u : Tm Γ) (HL((pu : tyOf u ≡ U))) → Ty Γ
  El[]  : (HL((q : tyOf (u [ τ ]t) ≡ U)))
    → (El u (HL(pu))) [ τ ]T ≡ El (u [ τ ]t) (HL(q))
\end{code}

For the type |𝔹| of Boolean, its code |𝕓| is introduced with a type equality |El𝕓| such that the elements of |𝕓| are exactly |𝔹|:
\begin{code}
data _ where
  𝕓     : Tm Γ
  𝕓[]   : 𝕓 [ σ ]t ≡ 𝕓

tyOf 𝕓          = U
tyOf (𝕓[] σ i)  = U[] {σ = σ} i

data _ where
  El𝕓 : El {Γ} 𝕓 refl ≡ 𝔹
\end{code}

For the |Π|-type, we again need a specialised substitution lifting.
This continues the pattern of introducing superfluous constructors to satisfy proof obligations (differences again highlighted).
\begin{code}
data _ where
  El[]₂ : (u : Tm Δ) (pu : tyOf u ≡ U)
    → (HL((pu₂ : tyOf (u [ σ ]t) ≡ U)))
    → tyOf (π₂ {Γ , El (u [ σ ]t) (HL(pu₂))} idS)
    ≡ El u pu [ σ ∘ π₁ idS ]T

_↑El : (σ : Sub Γ Δ) {u : Tm Δ}
  {pu : tyOf u ≡ U} (HL({pu' : tyOf (u [ σ ]t) ≡ U}))
  → Sub (Γ , (HL(El (u [ σ ]t) pu'))) (Δ , El u pu)
(σ ↑El) {u} {pu} {pu'} =
  σ ∘ π₁ idS , π₂ idS ∶[ (HL(El[]₂ u pu pu')) ]
\end{code}

Finally, we introduce the code |π| for |Π| and the type equality |Elπ| to complete our definition of type theory using QIIRT:
\begin{code}
data _ where
  π    :  (a : Tm Γ) (HL((pa : tyOf a ≡ U)))
          (b : Tm (Γ , El a pa)) (HL((pb : tyOf b ≡ U))) → Tm Γ
  π[]  :  (a : Tm Γ)              (HL((pa : tyOf a ≡ U)))
       →  (b : Tm (Γ , El a pa))  (HL((pb : tyOf b ≡ U)))
       →  (HL((pa' : tyOf (a [ σ ]t) ≡ U)))
       →  (HL((pb' : tyOf (b [ σ ↑El ]t)  ≡ U)))
       →  (π a pa b pb) [ σ ]t
       ≡  π (a [ σ ]t) (HL(pa')) (b [ σ ↑El ]t) (HL(pb'))

tyOf (π _ _ _ _) = U

data _ where
  Elπ : (a : Tm Γ) (HL((pa : tyOf a ≡ U)))
    → (b : Tm (Γ , El a pa)) (HL((pb : tyOf b ≡ U)))
    → El (π a pa b pb) (HL(refl)) ≡ Π (El a pa) (El b pb)

tyOf (π[] _ _ _ _ _ _ i) = U[] i
\end{code}

In the end, we emphasise that the introduction of superfluous equality proofs and constructors only makes sense under the assumption of UIP.
These additional arguments are essentially unique and thus do not add any new laws to type theory, but merely serve as devices to meet the syntactic restriction of strict positivity in the current implementation of \CA.

\subsection{Recursion and elimination principles} \label{sec:tt:elim}
We turn to recursion and elimination principles for our syntax.
Our QIIRT definition yields an \emph{initial model}.
This means that for any other model (algebra) of our theory, there is a unique structure-preserving map from our syntax to that model.
The recursion and elimination principles make this property concrete.
Here, we only discuss the part for substitution calculus, since other type formers are addressed similarly.
For the interested reader, see our formalisation.

The signature for an algebra is packed in a record type~|SC| (short for Substitution Calculus).
Inductive types and the function |tyOf| are interpreted as indexed types and a function between sets.
Constructors of our syntax, except superfluous ones, correspond to function fields in this record, including equality constructors and clauses of |tyOf|.
\begin{code}
record SC  : Set  where
  field
    Ctx     : Set
    Ty      : Ctx → Set
    Tm      : Ctx → Set
    Sub     : Ctx → Ctx → Set
    tyOf    : Tm Γ → Ty Γ

    ∅       : Ctx
    _,C_    : (Γ : Ctx)(A : Ty Γ) → Ctx
    _[_]T   : (A : Ty Δ)(σ : Sub Γ Δ) → Ty Γ
    _[_]t   : (t : Tm Δ)(σ : Sub Γ Δ) → Tm Γ
    idS∘_   : idS ∘ σ ≡ σ
    ...
    βπ₂     : π₂ (σ , t ∶[ p ]) ≡ t
    ...
    tyOf[]  : tyOf (t [ σ ]t)      ≡ (tyOf t) [ σ ]T
    tyOfπ₂  : tyOf (π₂ {A = A} σ)  ≡ A [ π₁ σ ]T
\end{code}

To distinguish syntactic constructors from the semantic methods in |SC|, we qualify the syntactic constructors with `|S.|' in the following discussion.

Superfluous equality constructors, like |S.tyOfπ₂idS|, are not required as fields in the record.
Instead, their semantic counterparts are defined within any given model using the other methods.
For example,
\begin{code}
  tyOfπ₂idS : (σ : Sub Γ Δ) (A : Ty Δ)
    → tyOf (π₂ {A = A [ σ ]T} idS) ≡ A [ σ ∘ π₁ idS ]T
  tyOfπ₂idS σ A = tyOfπ₂ idS ∙ [∘]T _ _ _
\end{code}
This simplifies the definition of models, as we only need to provide interpretations for the essential constructors.

The recursion principle consists of a family of functions that map syntax to their semantic counterparts:
\begin{code}
recCtx   : S.Ctx      → Ctx
recTy    : S.Ty Γ     → Ty (recCtx Γ)
recTm    : S.Tm Γ     → Tm (recCtx Γ)
recSub   : S.Sub Γ Δ  → Sub (recCtx Γ) (recCtx Δ)
\end{code}
We also need a function that translates proofs about syntactic equalities into semantic equalities:
\begin{code}
recTyOf  : S.tyOf t ≡ B → tyOf (recTm t) ≡ recTy B
\end{code}
The definition of these functions proceeds by pattern matching on the syntactic structure.
Each clause is an application of the corresponding method from the |SC| record:
\begin{code}
recCtx S.∅                = ∅
recCtx (Γ S., A)          = recCtx Γ ,C recTy A
...
recSub (σ S., t ∶[ pt ])  = recSub σ , recTm t ∶[ recTyOf t pt ]
...
\end{code}
The most interesting case is perhaps |recTyOf|, which handles the translation of syntactic equations.
For a given syntactic equality proof |p : S.tyOf t ≡ B|, we must construct a semantic equality proof.
This is done by applying |recTy| to both sides of the syntactic equality to get |recTy (S.tyOf t) ≡ recTy B|, and then using the semantic counterpart of the |tyOf| clause to derive |tyOf (recTm t) ≡ recTy (S.tyOf t)|.
Taking |S.π₂| as an example, we have:
\begin{code}
recTyOf {B = B} (S.π₂ {A = A} σ) p =
  tyOf (recTm (S.π₂ σ))         ≡⟨⟩
  tyOf (π₂ (recSub σ))          ≡⟨ tyOfπ₂ (recSub σ) ⟩
  (recTy A) [ π₁ (recSub σ) ]T  ≡⟨⟩
  recTy (A S.[ S.π₁ σ ]T)       ≡⟨⟩
  recTy (S.tyOf (S.π₂ σ))       ≡⟨ cong recTy p ⟩
  recTy B                       ∎
\end{code}
The coherence conditions for |recTyOf| over equality constructors are trivial because of UIP.

For the elimination principle, we consider the notion of displayed algebras over an |SC|-algebra |M|, as a record type |SC∙| parametric in |M|, and later instantiate |M| to the term algebra, i.e.\ the syntax.
Carriers of a displayed algebra as well as the semantics of |tyOf| are given below.
\begin{code}
record SC∙ (M : SC) : Set where
  open SC M

  field
    Ctx∙   : Ctx → Set
    Ty∙    : Ctx∙ Γ → Ty Γ → Set
    Tm∙    : Ctx∙ Γ → Tm Γ → Set
    Sub∙   : Ctx∙ Γ → Ctx∙ Δ → Sub Γ Δ → Set
    tyOf∙  : Tm∙  Γ∙ t → Ty∙ Γ∙ (tyOf t)
\end{code}
As motives are indexed by their underlying model, we will have equations over equations of the underlying model.
It is convenient to specialise dependent paths for them, e.g.,
\begin{code}
  _≡Tm[_]_ : Tm∙ Γ∙ t → t ≡ u → Tm∙ Γ∙ u → Set
  _≡Tm[_]_ {Γ∙ = Γ∙} t∙ e u∙ =
    PathP (λ i → Tm∙ Γ∙ (HL((e i)))) t∙ u∙
\end{code}
The signature for |SC∙|-algebras is similar to the one for |SC|-algebras.
The difference here is that each displayed operation is indexed by their underlying operation and thus equations become equations over equations.
\begin{code}
  field
    ∅∙       : Ctx∙ ∅
    _,∙_     : Ctx∙ Γ → Ty∙ Γ∙ A → Ctx∙ (Γ ,C A)
    _[_]T∙   : Ty∙ Δ∙ A → Sub∙ Γ∙ Δ∙ σ → Ty∙ Γ∙ (A [ σ ]T)
    _[_]t∙   : Tm∙ Δ∙ t → Sub∙ Γ∙ Δ∙ σ → Tm∙ Γ∙ (t [ σ ]t)
    tyOf[]∙  : tyOf∙  (t∙ [ σ∙ ]t∙) ≡Ty[ tyOf[] ] (tyOf∙ t∙ [ σ∙ ]T∙)
    ...
    [idS]t∙  : t∙                    ≡Tm[ [idS]t ]  t∙ [ idS∙ ]t∙
    [∘]t∙    : t∙ [ τ∙ ]t∙ [ σ∙ ]t∙  ≡Tm[ [∘]t ]    t∙ [ τ∙ ∘∙ σ∙ ]t∙
\end{code}
Note that if |[idS]t| in its QIIT definition is formulated with a dependent path, the equality proof in the middle of |_≡Tm[_]_| has to be a dependent path.
As a result, we would have to specify two underlying equations as
\begin{code}
  t∙ ≡Tm[ (HL([idS]T)) ][ (HL([idS]t)) ] t∙ [ idS∙ ]t∙
\end{code}
and equational reasoning with them would involve three equations altogether.
It is nice that we do not have to deal with this extra proof obligation in our formulation.

The elimination principle is stated similarly to the recursion principle but indexed over the term algebra~(\Cref{sec:meta:term}),
\begin{code}
elimCtx   : (Γ :  S.Ctx)      → Ctx∙ Γ
elimTy    : (A :  S.Ty Γ)     → Ty∙ (elimCtx Γ) A
elimTm    : (t :  S.Tm Γ)     → Tm∙ (elimCtx Γ) t
elimSub   : (σ :  S.Sub Γ Δ)  → Sub∙ (elimCtx Γ) (elimCtx Δ) σ
elimTyOf  : (t :  S.Tm Γ) (p : S.tyOf t ≡ A)
  →  tyOf∙ (elimTm t) ≡Ty[ p ] elimTy A
\end{code}

For the coherence conditions in the definition of the eliminators, we may need additional reasoning steps instead of just using the semantics equation, so we use transitivity of dependent paths:
\begin{code}
_∙P_ :  {x' : B x}{y' : B y}{z' : B z}
  → {p : x ≡ y}{q : y ≡ z}
  → PathP (λ i → B (p i)) x' y' → PathP (λ i → B (q i)) y' z'
  → PathP (λ i → B ((HL((p ∙ q)))i)) x' z'
\end{code}
We also use UIP to identify the highlighted |p ∙ q| with the desired underlying equation in special-purpose equational reasoning combinators such as the following:
\begin{code}
  beginSub[_]_
    : ({p} q : σ ≡ τ) → σ∙ ≡Sub[ p ] τ∙ → σ∙ ≡Sub[ q ] τ∙
  beginSub[_]_ {σ∙} {τ∙} {p} q p∙ =
    subst (λ r → σ∙ ≡Sub[ r ] τ∙) (UIP p q) p∙
\end{code}

For example, the coherence proof for |ηπ| is given by
\begin{code}
beginSub[ ηπ ]
  elimSub σ
    ≡Sub[ ηπ ]⟨ ηπ∙ (elimSub σ) ⟩
  π₁∙ (elimSub σ) ,
  π₂∙ (elimSub σ) ∶[ refl , tyOfπ₂∙ (elimSub σ) ]t∙
    ≡Sub[ refl ]⟨ cong (λ z → ... , ... ∶[ refl , z ]t∙) (UIP _ _) ⟩
  π₁∙ (elimSub σ) ,
  elimTm (π₂ σ) ∶[ refl , elimTyOf (π₂ σ) refl ]t∙
    ∎
\end{code}
with the steps |σ∙ ≡Sub[ p ]⟨ p∙ ⟩ τ∙| implemented using |_∙P_|.
These steps give us an equation over |ηπ ∙ (refl ∙ refl) |, and |beginSub[ ηπ ]_| gives us an easy way to correct this to an equation over |ηπ| as desired instead.


\subsection{Practical workarounds for mutual definitions}  \label{sec:tt:mutual}

So far, we have outlined how the recursion and elimination principles should be defined \emph{ideally}.
In practice, however, limitations (and occasional mysterious bugs) of the proof assistant require us to adopt certain workarounds in order to implement the intended definitions.
%This shows that the current design of \CA is not yet fully aligned with the theory of quotient inductive-inductive types~\cite{Kaposi2019}.

\paragraph{Mutually interleaved QIITs}
Constructors of QIITs currently can not be interleaved in \CA~\cite{Agdaissue2021}, even within an |interleaved mutual| block.
The reason is that such a block is desugared into a collection of forward declarations for the |data| types, rather than for the constructors.
In principle, all constructors belonging to the same family of QIITs should be declared within the same context~\cite{Kaposi2019}.
However, due to this desugaring, equality constructors may end up depending on other constructors that are not yet in scope.

We work around this issue as follows:
\begin{enumerate*}[label=(\roman*)]
  \item we make forward declarations for the \emph{entire definition} of the QIITs, including the constructors;
  \item we introduce each constructor but only refer to forward declarations when referring to other constructors;
  \item we define the forward declarations by their corresponding constructors;
  \item finally, we expose only the actual constructors, omitting the forward declarations.
\end{enumerate*}
The following snippet illustrates this approach:
\begin{code}
module S where
  data Ctx  : Set
  ...
  ∅    : Ctx -- note indentation, not a constructor!
  _,_  : (Γ : Ctx)(A : Ty Γ) → Ctx
  ...
  data Ctx where
    ∅'    : Ctx -- this is a constructor
    _,'_  : (Γ : Ctx) (A : Ty Γ) → Ctx
  ...
  ∅       = ∅' -- make definition for forward declarations
  _,_     = _,'_
  ...
open S public -- expose actual constructors
  hiding ( ∅ ; _,_; ...)
  renaming ( ∅' to ∅ ; _,'_ to _,_; ...)
\end{code}

This translation from QIITs in theory to their actual definitions in \CA should be sufficient to define mutually interleaved QIITs.
Indeed, pedagogical presentations of type theory typically introduces one type former at a time, together with its formation, introduction, elimination, and equality rules (see, e.g.~\cite{Hofmann1997}), rather than presenting all type formers at once using a few large monolithic sets of rules.

\paragraph{Mutual interleaved QIIRTs}
Interleaving function clauses with inductive types is a different matter, since we cannot forward declare a function clause together with its computational behaviour.\footnote{Custom rewrite rules are not allowed in \CA.}
However, because we have `Forded' the typing constraints into equality proofs, what we actually need at the point of introducing constructors is only the existence of such an equality proof, not its computational content.

Our workaround is therefore as follows:
\begin{enumerate*}[label=(\roman*)]
  \item we declare the existence of the required equality proof before it is used,
  \item we define |tyOf| only after all datatype declarations have been given, and
  \item we provide the actual definition corresponding to the forward declaration.
\end{enumerate*}
For instance, the equality constructor |ηπ| asks for a proof of |tyOf (π₂ σ) ≡ A [ π₁ σ ]T|.
In this case, we simply forward declare such a proof:
\begin{code}
tyOfπ₂  : tyOf (π₂ σ) ≡ A [ π₁ σ ]T
ηπ      : σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ ])
\end{code}
Then, once |tyOf| has been defined, we simply set |tyOfπ₂| to |refl|:
\begin{code}
tyOf (π₂' {Γ} {Δ} {A} {σ}) = A [ π₁ {A = A} σ ]T
...
tyOfπ₂ = refl
\end{code}

This translation is valid as long as the computational behaviour of the interleaved function clauses is not needed up to judgemental equality.

\paragraph{Mutually-defined functions}
\LT[noinline]{(Low) Create an Agda issue?}
Since the constructors of QII(R)Ts can be mutually interleaved, their recursion and elimination principles also need to be given in the same vein.
However, \Agda does not allow us to interleave clauses of different functions directly.
One workaround is to use forward declarations as a lifting of the entire clause and then perform the necessary coercions along the corresponding equality proofs by hand.

Another possibility is to define a single family of functions indexed by tags.
For instance, the recursion principle can be implemented by introducing a datatype |Tag| with one constructor for each motive:
\begin{code}
data Tag : Set where
  ctx ty sub tm tyof : Tag
\end{code}
Then, we define the recursion principle uniformly as |rec|, with |tyOfRec| computing its type.
Each actual function is introduced as a synonym for |rec| at the appropriate tag:
\begin{code}
tyOfRec : Tag    → Set
rec : (t : Tag)  → tyOfRec t
tyOfRec ctx   = S.Ctx → Ctx

rec ctx S.∅              = ∅
rec ctx (Γ S., A)        = rec ctx Γ ,C rec ty A
...

recCtx   = rec ctx
...
\end{code}

At the time of writing, however, this encoding cannot be fully carried out in \CA: some terms that should be strictly equal are not recognised as such during type checking.
For example, in the following clause of |rec|:
\begin{code}
rec sub (S._,_∶[_] {Γ} {Δ} {A} σ t p) = _,_∶[_]
  {rec ctx Γ} {rec ctx Δ} {rec ty A} (rec sub σ) (rec tm t)
  (HL({! rec tyof t p !}))
\end{code}
the subterm in the hole is accepted by \Agda, but refining it results an error, as the terms |rec ty (A S.[ σ ]T)| and |rec ty A [ rec sub σ ]T| are not recognised as equal --- even though the former was already defined to be the latter.

In our formalisation, we fall back on forward declarations alone with coercions.
We are still investigating the root cause of this behaviour, but it may point to a design flaw.


\section{Metatheory}\label{sec:meta}
Having defined type theory as QIIRTs, we now turn to models of type theory as well as constructions of new models from existing ones.

%We find that reasoning with this definition \emph{per se} in \CA is hard even with substitution calculus: the lack of strict equalities in type theory is known to cause the transport hell~\cite{Altenkirch2016a} and even worse it cannot be mitigated by using custom rewriting rules~\cite{Cockx2020,Cockx2021} in \CA.
%Nevertheless, programming with type theory seems doable, as normalisation can be

\subsection{Term model} \label{sec:meta:term}
The term model is a self-interpretation of syntax, allowing displayed models to be instantiated over it and ensuring that the elimination rule computes.
The definition is routine: each field is interpreted by the corresponding constructor, except that additional equality constraints (such as the one in |βπ₂| highlighted below) are replaced by actual proofs:
\begin{code}
Term : SC
Term = record
  { ∅       = S.∅
  ; tyOf[]  = refl
  ...
  ; βπ₂     = λ {Γ} {Δ} {A} σ t p
    → S.βπ₂ σ t p (HL((cong (A [_]T) (S.βπ₁ σ t p) ∙ sym p))) }
\end{code}

Other type formers are given similarly.
The recursion and elimination principles justify that the term model is indeed the initial model.

\subsection{Standard model} \label{sec:standard-model}

In the standard model, contexts are interpreted as sets in \CA, types as sets indexed by a context~|Γ|, substitutions as functions between these sets, and terms as \emph{pairs} |(A, t)| consisting of an interpreted type |A : Γ → Set| together with a dependent function |t : (γ : Γ) → A γ|.
The interpretation of |tyOf| is simply the first component |A|.
In other words, terms are interpreted as a type |A|, together with a `section' |t : (γ : Γ) → A γ| of that type, as usual:
\begin{code}
  std : SC
  std .Ctx              = Set
  std .Ty  Γ            = Γ → Set
  std .Sub Γ Δ          = Γ → Δ
  std .Tm  Γ            = Σ[ A ∈ (Γ → Set) ] ((γ : Γ) → A γ)
  std .tyOf (A , t)     = A
\end{code}

The main construction of the model is the same as in the standard model of type theory using QIITs~\cite[Section~4]{Altenkirch2017}, except that the typing constraint |p| in |σ , t ∶[ p ]| is `Forded'.
As a result, the value |t γ| below must be transported along |p|, as highlighted below:
\begin{code}
  std .∅                = Unit
  std ._,C_ Γ A         = Σ Γ A
  std ._[_]T A σ γ      = A (σ γ)
  std ._[_]t (A , t) σ  = (λ γ → A (σ γ)) , (λ γ → t (σ γ))
  std .tyOf[]           = refl
  ...
  std ._,_∶[_] σ (A , t) p γ = (σ γ , (HL(transport (λ i → p i γ) (t γ))))
\end{code}

To extend the standard model for the universe |U|, we define a Tarski universe of codes and its interpretation
\begin{code}
data UU : Set
T : UU → Set

data UU where
  bool : UU
  pi : (a : UU) → (T a → UU) → UU

T : UU → Set
T bool      = Bool
T (pi a b)  = (x : T a) → T (b x)
\end{code}
Each of the constructs in \Cref{sec:tt:univ} can now be interpreted:
\begin{code}
std  .U   _             = UU
std  .U[]               = refl
std  .El  (A , u) pu γ  = T (subst (λ A → A γ) pu (u γ))
std  .𝕓                 = (λ _ → UU) , λ _ → bool
std  .π (A , a) pa (B , b) pb = (λ _ → UU) , λ γ → pi
   (transport (λ i → pa i γ) (a γ))
   (λ a → transport (λ i → pb i (γ , a)) (b (γ , a)))
...
\end{code}
Coherence conditions are then verified using standard properties of transport.
We have formalised the standard model for type theory with $\Pi$-types, Booleans, and a Tarski universe, except the case for |π[]|.

The main effort in the formalisation arises from the lack of \emph{regularity}~\cite{Sterling2022}: there is a path |transportRefl| between the transport along reflexivity and the identity but they are not strictly equal.
For instance, the coherence condition for |Π[]| is given as
\begin{code}
stdPi .Π[] {Γ} {Δ} {A} σ B i γ =
  (a : A (σ γ)) → B (σ γ , transportRefl³ a) (~ i))
\end{code}
where |transportRefl³| amounts to using |transportRefl| three times.
The case |π[]| above involves an equation over a transport of another transported term.
If regularity were available, this would collapse to the trivial reflexivity proof.
\LT[noinline]{try to finish it if we have time.}

\subsection{Normalisation by evaluation, and the logical predicate interpretation} \label{sec:nbe}
We implement normalisation by evaluation (NbE) for the substitution calculus.
Following the approach for type theory~\cite{Altenkirch2017}, we define inductive-recursively both the type of variables (with their embedding into terms) and the type of renamings (with their embedding into substitutions).
The implementation is straightforward, so we omit the details here.
In the end, this yields a normalisation function that produces, for every term, a de Bruijn variable and computes:
\begin{code}
normalise : (t : Tm Γ) → Σ[ tⁿ ∈ NeTm Γ ] t ≡ ⌜ tⁿ ⌝
\end{code}
Compared to NbE for substitution calculus using QIITs, our formalisation is simpler: no transports appear at all, because variables and terms are not indexed by their types.

The picture is very different for the logical predicate interpretation.
Although NbE works cleanly, the logical predicate interpretation --- often considered a benchmark challenge~\cite{Abel2019} for language formalisation --- remains at least as difficult as in the QIIT-based setting, even for substitution calculus.

To see why, recall that the motives for |Ctx| and |Ty| in the logical predicate interpretation are given by
\begin{code}
record Ctxᴾ (Γ : Ctx) : Set where
  field
    ctxᴾ : Ctx
    wkᴾ  : Sub ctxᴾ Γ

Tyᴾ : Ctxᴾ Γ → Ty Γ →  Set
Tyᴾ Γᴾ A = Ty (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ]T)
\end{code}
Here the typing constraint |(ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ]T)| already shares the familiar shape of |Tm Γ A|, but with an additional complication: the index explicitly demands a type substitution.
Since the QIIRT representation only provides equality constructors for type substitutions, the development quickly results in repeated and tedious use of transports.

In short, NbE benefits directly from removing typing indices and avoids transports altogether, whereas the logical predicate interpretation still inherits the need for coercions with type substitutions.
We did not bother to finish all cases of the logical predicate interpretation, as Altenkirch and Kaposi~\cite{Altenkirch2016a} have already shown that such tedious use of transports is possible (but impractical) in theory.

\subsection{Strictification} \label{sec:strictify}
Instead, we turn our attention to \emph{strictification}~\cite{Donko2022,Kaposi2025}: given a model of type theory, certain equality constructors can be made strict (i.e., made to hold judgementally) to form a new model.
A familiar analogy is the transition from lists to difference lists, where a list is represented by a list-appending function and list concatenation is function composition, which is associative judgementally.

In the same spirit, we may attempt to `strictify' the category part of substitution calculus using the Yoneda embedding, so that the unit laws and associativity law hold strictly, \emph{modulo} the property of naturality.
Given any |SC|-algebra, we define a presheaf interpretation of |Sub| by
\begin{code}
record Subʸ (Γ Δ : Ctx) : Set where
  constructor _,_
  field
    y    : ∀{Θ} → Sub Θ Γ → Sub Θ Δ
    nat  : (τ : Sub Ξ Θ) (δ : Sub Θ Γ) → y δ ∘ τ ≡ y (δ ∘ τ)
\end{code}
By UIP, any two morphisms |σ| and |σ'| in the presheaf category are equal whenever their functionals agree:
\begin{code}
≡ʸ→≡ : {σ σ' : Subʸ Γ Δ} → σ ≡ʸ σ' → σ ≡ σ'
\end{code}
where |_≡ʸ_| denotes the path type between their functionals.
Completing the Yoneda embedding then gives us strict unit and associativity laws, up to |≡ʸ→≡|:
\begin{code}
Yoneda .idS∘_   _      = ≡ʸ→≡ refl
Yoneda ._∘idS   _      = ≡ʸ→≡ refl
Yoneda .assocS  _ _ _  = ≡ʸ→≡ refl
\end{code}
We can adapt the local universe construction~\cite{Lumsdaine2015,Donko2022} for |M : SC| to further strictify the laws for type substitutions for substitution.
Types under the context $\Gamma$ in the local universe construction are interpreted as a triple consisting of a context $V$ as the local universe, a type under the context $V$, and a substitution from $\Gamma$ to $V$:
\begin{code}
record Ty³ (Γ : Ctx) : Set where
  constructor ty³
  field
    V : Ctx
    E   : Ty V
    ⌜_⌝ : Sub Γ V
\end{code}
Type substitution is defined by `delaying' the substitution, i.e., by viewing the substitution |⌜ A ⌝| as an accumulator parameter.
Then, we can show that the laws about type substitution boil down the right unit and the associativity laws for substitutions:
\begin{code}
  (M !) .[idS]T {Γ} {A}  =
    cong (ty³ (A .V) (E A)) (HL((sym (⌜ A ⌝ ∘idS))))
  (M !) .[∘]T A σ τ      =
    cong (ty³ (A .V) (E A)) (HL((assocS σ τ ⌜ A ⌝)))
\end{code}
If |M| is strictified by the Yoneda embedding, then the laws for identity substitution and substitution composition in |M !| will be strict up to |≡ʸ→≡|.
Hence, combining both techniques, we can construct models where both the category laws and substitution laws are strict after applying |≡ʸ→≡|.

Nevertheless, strictification does \emph{not} resolve our difficulties with the logical predicate interpretation.
In particular, the lack of strict propositions (or just definitional UIP) in \CA prevents |σ ≡ʸ σ'| from being strictly equal, since the paths between their properties must still be identified manually using UIP.
Although \Agda provides a form of strict propositions |Prop|, it is not designed to work with \CA and interacts poorly with cubical primitives for now~\cite{Agda-issue2022}.
As a consequence, coercions along equations identified by UIP remain unavoidable.

\section{Discussion and conclusion}
\label{sec:discussion}

\FNF{Also discuss alternative choices such as basing the formalisation on (split) comprehension categories, see Brunerie and de Boer (R2)}

It is well known that type theory in type theory is possible in theory, but in practice its formalisation often requires giving up some of the support and safety checks provided by proof assistants.
From one point of view, our work addresses the following question: is there any existing type-theoretic proof assistant that can formalise the intrinsic representation of type theory using QIITs reliably, without compromise?
Based on our experimental formalisation in \CA, our answer is regrettably: not yet.

\paragraph{Comparison with QIIT approaches}
Previous formalisations~\cite{Kaposi2019,Kaposi2017,Altenkirch2016a,Altenkirch2017} based on the CwF semantics of type theory using QIITs have resorted to using postulated constructors and custom rewrite rules to manually define QIITs and their eliminators.
However, this comes at a cost: the proof assistant no longer performs strict positivity, coverage, or termination checks for functions defined from quotient inductive types, nor does it supports dependent pattern matching, program extraction, and interactive theorem proving.
The loss of coverage check for inductive types is mitigated by using hand-crafted eliminators (see \Cref{sec:tt:elim}), since the coverage check is also in effect for record types.

The Ehrhard's style of presentation~\cite{Coquand2020,Ehrhard1988}, whereas the set of terms remains indexed by types but without any transport in the middle of terms for specifying equations, can be stated by using dependent paths and has been adopted by a recent formalisation~\cite{Altenkirch2026} in \CA.

Our approach leads to no transports appearing in its own syntax and also avoids the use of dependent paths at all.
However, the same transports (and the same equations for them) seem to have a tendency to come back in concrete model constructions, as explained in \cref{sec:meta}.

We remark that the lack of transports is an advantage for avoiding strict positivity issues in the current implementation of \CA.
By using native features such as higher inductive types, rather than postulates in ordinary \Agda, we do get computational interpretations.
For example, our implementation of normalization by evaluation in \cref{sec:nbe} can actually normalise terms and could be potentially extracted as Haskell programs with the cubical information explicitly erased using \Agda's \verb|--erased-cubical| feature.

\paragraph{Strictification}
Kaposi and Pujet~\cite{Kaposi2025} have shown how strictification techniques can simplify proofs, but this is an orthogonal issue.
Even though strictification turns most of the equality constructors about substitution to strict equalities, this does not help with transports appearing in the QIIT definition of terms and the resulting strict positivity issues, as strictification can only be applied \emph{after} the inductive types are defined.
In \cref{sec:strictify}, we have sketched how also our notion of models can be strictified using a simpler idea.
However, a proper strictification may require a different metatheory than `just' the support of QII(R)Ts (see below).

% Untyped version might still be easiest to work with, with current proof assistant technology

\paragraph{A proper syntax for HII(R)Ts}
The syntax for declaring higher inductive-inductive types and QIITs in \CA falls short of their theoretical capabilities~\cite{Kaposi2020b,Kaposi2019}.
As shown in \Cref{sec:tt:cwf}, the legitimate definition of type theory based on CwF with transports violates the syntactic restriction of strict positivity in \CA.
Even though transport hell is better avoided in practice, this is not a justification for excluding otherwise valid definitions.
The alternative definition, based on natural models, does not violate strict positivity but still requires forward declarations (\Cref{sec:tt:mutual}) to overcome the inconvenience of syntax.

\paragraph{A theory of QIIRTs}
We work around the problem by defining type theory using QIIRTs, but this raises another question: what is the theory of QIIRTs, anyway?

Different forms of QIITs and inductive-recursive types (IRTs) have been used to develop type theory in type theory.
Large and infinitary IRTs are used for the standard model of universe; small inductive-recursive types~\cite{Hancock2013} for implementing normalisation by evaluation~\cite{Altenkirch2017}; QIITs and QIIRTs for the intrinsic representations of type theory.
Note further that the target of |tyOf| is the inductive type |Ty| being defined simultaneously, so the QIIRTs used to define our representation is neither large nor small.
Nevertheless, we expect that the encoding of small inductive-recursive types as indexed inductive types still applies to this `self-referring' induction-recursion, as we have derived our representation by `undoing' the encoding.

A framework to encompass all variants will be convenient for proof assistant implementation.
Such a scheme may be developed by extending the type theory of QIITs~\cite{Kaposi2019,Kovacs2020a} with an additional construct to distinguish strict and weak equalities and a coverage condition for function clauses.

\paragraph{The support of interleaved mutual definitions}
Another challenge concerns interleaved mutual definitions.
Since constructors of QIITs may be mutually interleaved, the elaboration from dependent pattern matching to eliminators need to take this into account.
Our workaround, using forward declarations to lift function clauses to fix the dependency, sacrifices their computational behaviour.
Furthermore, our definitions appear to reach the limits of the termination checker: even seemingly harmless functions when defining the recursion principle fail to pass termination checking.
\LT{Clarify the termination issue in \Cref{sec:tt:elim}}

% \paragraph{The need for strict propositions}
\paragraph{Strict propositions, and observational type theory}
The recent work on strictified syntax~\cite{Kaposi2025} addresses transport hell using observational type theory (OTT)~\cite{Pujet2022,Pujet2023,Pujet2024}, with strict propositions in the metatheory playing a central role.
While \Agda does support strict propositions~\cite{Gilbert2019}, this feature was not designed to work with \CA~\cite{Agda-issue2022}.
%
%\paragraph{The implementation of OTT or XTT}
To formalise the metatheory of type theory using QIITs with as few transports as possible, it seems inevitable to use a different metatheory rather than the off-the-shelf metatheory offered by \CA.
In particular, regularity and definitional UIP, supported by OTT (see \cite{Altenkirch2019,Pujet2024} for the discussion on regularity) and by its cubical variant XTT~\cite{Sterling2022}, would immediately simplify our standard model~(\Cref{sec:standard-model}) and make the Yoneda embedding and the local universe construction usable as strictification techniques.

The use of QIITs in OTT~\cite{Kaposi2025} in \Agda requires the user themselves to implement the coercion rules for inductive types~\cite{Pujet2024} as well as their elimination principles.
Quotient inductive types are not supported in the implementation of OTT in Rocq~\cite{Pujet2024a} and its theory is still being developed~\cite{Felicissimo2025a}.

A new option \verb"--cubical=no-glue" in the forthcoming \Agda 2.9.0~\cite{Agda-issue2025} disallows the |Glue| type in the cubical mode and in principle forms a cubical type theory compatible with the uniqueness of identity proofs.
Since \CA already supports HIITs (though with caveats noted earlier), implementing XTT with QIITs as a variant of \CA may be within reach~\cite{Agda-issue2019}.


\paragraph{The Ford transformation and definitional UIP}
The Ford transformation is known to work well with definitional UIP~\cite{Altenkirch2006}.
So far, we have only `Forded' the \verb|Tm| constructors, but what if every constructor were Forded, with indices removed entirely?
The resulting representation of type theory would remain intrinsic, but all typing constraints would appear as equality proofs, which are definitionally proof-irrelevant in XTT or OTT.
This could provide a way to escape transport hell without relying on strictification.

Of course, explicitly transforming these typing constraints to equality proofs would still be tedious and error-prone, so an elaboration from QIITs to their Forded presentation using QIIRTs would be useful.
The connection between QIITs and its Forded definition with the index eliminated echoes the notion of reornament~\cite{Dagand2014,Ko2016,Dagand2017}, so this translation itself may be of interest in general.

\paragraph{Conclusion}
There are still gaps between a pen-and-paper type theory and a fully formalised type theory in a proof assistant, on both the theoretical and practical sides.
Without further advances in the technology of proof assistants, formalising type theory intrinsically within a proof assistant remains a difficult task.
We hope that the lessons learned here can help the design of future proof assistants, so that one day we may implement a proof assistant within a proof assistant without (too much) sweat and tears.

\begin{acks}
  We appreciate the constructive comments from the anonymous reviewers, in particular the pointers to alternative ways to formalising type theory that we overlooked initially.
  Our syntax for displayed equations in \cref{sec:tt:elim} is inspired by the syntax of equational reasoning for displayed categories on 1Lab~\cite{Amlia2025}.
  We are also grateful to Shu-Hung You for his comments on the early draft.
  The work is supported by the National Science and Technology Council of Taiwan under grant NSTC 114-2222-E-001-001-MY3.
\end{acks}

\IfFileExists{./reference.bib}{\bibliography{reference}}{\bibliography{ref}}
%\bibliography{ref}

\end{document}



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "main.tex"
%%% eval: (add-hook 'after-save-hook (lambda () (shell-command "make tex")) t)
%%% End:
