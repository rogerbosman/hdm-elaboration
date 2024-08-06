;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((coq-mode . ((company-coq-dir-local-symbols . (
    ("⊢a" . (?⊢ (Br . cl) ?a))
    ("⊢σ" . (?⊢ (Br . cl) ?σ))
    ("⊢τ" . (?⊢ (Br . cl) ?τ))
    ("⊢θ" . (?⊢ (Br . cl) ?θ))
    ("⊢d" . (?⊢ (Br . cl) ?d))
    ("⊢dp" . (?⊢ (Br . cl) ?d (Br . cl) ?p))
    ("⊢t" . (?⊢ (Br . cl) ?t))
    ("⊢t≈" . (?⊢ (Br . cl) ?t (br . bl) ?≈))


    ("⊢wfσ" . (?⊢ (Br . cl) ?w (br . bl) ?f (br . bl) ?σ))
    ("⊢wfτ" . (?⊢ (Br . cl) ?w (br . bl) ?f (br . bl) ?τ))
    ("⊢wft" . (?⊢ (Br . cl) ?w (br . bl) ?f (br . bl) ?t))

    ("=|" . ?⫤)

    ("≔__x" . (?≔ (Br . cl) ?x))
    ("≔__α" . (?≔ (Br . cl) ?α))
    ("▹__x" . (?▹ (Br . cl) ?x))
    ("⟧__ρ" . (?⟧ (Br . cl) ?ρ))
    ("↤__x" . (?↤ (Br . cl) ?x))

    ("::a" . (?∷ (Br . cl) ?a))
    ("::x" . (?∷ (Br . cl) ?x))
    ("::o" . (?∷ (Br . cl) ?o))

    ("≡α" . (?≡ (Br . cl) ?α))
    ("≡x" . (?≡ (Br . cl) ?x))
    ("≡αx" . (?≡ (Br . cl) ?α (br . bl) ?x))

    ("≊α" . (?≊ (Br . cl) ?α))
    ("≊x" . (?≊ (Br . cl) ?x))
    ("≊αx" . (?≊ (Br . cl) ?α (br . bl) ?x))

    ("∅τ" .  (?∅ (Br . cl) ?τ))
    ("∅σ" .  (?∅ (Br . cl) ?σ))
    ("∅t" .  (?∅ (Br . cl) ?t))
    ("∅τx" . (?∅ (Br . cl) ?τ (br . bl) ?x))
    ("∅σx" . (?∅ (Br . cl) ?σ (br . bl) ?x))

    ("∪τ" .  (?∪ (Br . cl) ?τ))
    ("∪σ" .  (?∪ (Br . cl) ?σ))
    ("∪t" .  (?∪ (Br . cl) ?t))
    ("∪τx" . (?∪ (Br . cl) ?τ (br . bl) ?x))
    ("∪σx" . (?∪ (Br . cl) ?σ (br . bl) ?x))

    ("∩τ" .  (?∩ (Br . cl) ?τ))
    ("∩σ" .  (?∩ (Br . cl) ?σ))
    ("∩t" .  (?∩ (Br . cl) ?t))
    ("∩τx" . (?∩ (Br . cl) ?τ (br . bl) ?x))
    ("∩σx" . (?∩ (Br . cl) ?σ (br . bl) ?x))

    ("∖τ" .  (?∖ (Br . cl) ?τ))
    ("∖σ" .  (?∖ (Br . cl) ?σ))
    ("∖t" .  (?∖ (Br . cl) ?t))
    ("∖τx" . (?∖ (Br . cl) ?τ (br . bl) ?x))
    ("∖σx" . (?∖ (Br . cl) ?σ (br . bl) ?x))

    ("≡τ" .  (?≡ (Br . cl) ?τ))
    ("≡σ" .  (?≡ (Br . cl) ?σ))
    ("≡t" .  (?≡ (Br . cl) ?t))
    ("≡τx" . (?≡ (Br . cl) ?τ (br . bl) ?x))
    ("≡σx" . (?≡ (Br . cl) ?σ (br . bl) ?x))

    ("⊆τ" .  (?⊆ (Br . cl) ?τ))
    ("⊆σ" .  (?⊆ (Br . cl) ?σ))
    ("⊆t" .  (?⊆ (Br . cl) ?t))
    ("⊆τx" . (?⊆ (Br . cl) ?τ (br . bl) ?x))
    ("⊆σx" . (?⊆ (Br . cl) ?σ (br . bl) ?x))

    ("∐τ" .  (?∐ (Br . cl) ?τ))
    ("∐σ" .  (?∐ (Br . cl) ?σ))
    ("∐t" .  (?∐ (Br . cl) ?t))
    ("∐τx" . (?∐ (Br . cl) ?τ (br . bl) ?x))
    ("∐σx" . (?∐ (Br . cl) ?σ (br . bl) ?x))

    ("∈τ" .  (?∈ (Br . cl) ?τ))
    ("∈σ" .  (?∈ (Br . cl) ?σ))
    ("∈t" .  (?∈ (Br . cl) ?t))
    ("∈τx" . (?∈ (Br . cl) ?τ (br . bl) ?x))
    ("∈σx" . (?∈ (Br . cl) ?σ (br . bl) ?x))

    ("∉τ" .  (?∉ (Br . cl) ?τ))
    ("∉σ" .  (?∉ (Br . cl) ?σ))
    ("∉t" .  (?∉ (Br . cl) ?t))
    ("∉τx" . (?∉ (Br . cl) ?τ (br . bl) ?x))
    ("∉σx" . (?∉ (Br . cl) ?σ (br . bl) ?x))


    ("⊆ψα" . (?⊆ (Br . cl) ?ψ (br . bl) ?α))
    ("⊆ψα#" . (?⊆ (Br . cl) ?ψ (br . bl) ?α (br . bl) ?#))
    ("⊆ψx" . (?⊆ (Br . cl) ?ψ (br . bl) ?x))
    ("⊆ψαx" . (?⊆ (Br . cl) ?ψ (br . bl) ?α (br . bl) ?x))

    ("≡ψx" . (?≡ (Br . cl) ?ψ (br . bl) ?x))

)))))
