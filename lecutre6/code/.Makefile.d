CoqIntro.vo CoqIntro.glob CoqIntro.v.beautified CoqIntro.required_vo: CoqIntro.v 
CoqIntro.vio: CoqIntro.v 
CoqIntro.vos CoqIntro.vok CoqIntro.required_vos: CoqIntro.v 
SyntaxInCoq.vo SyntaxInCoq.glob SyntaxInCoq.v.beautified SyntaxInCoq.required_vo: SyntaxInCoq.v 
SyntaxInCoq.vio: SyntaxInCoq.v 
SyntaxInCoq.vos SyntaxInCoq.vok SyntaxInCoq.required_vos: SyntaxInCoq.v 
denotationalSemantics.vo denotationalSemantics.glob denotationalSemantics.v.beautified denotationalSemantics.required_vo: denotationalSemantics.v SyntaxInCoq.vo
denotationalSemantics.vio: denotationalSemantics.v SyntaxInCoq.vio
denotationalSemantics.vos denotationalSemantics.vok denotationalSemantics.required_vos: denotationalSemantics.v SyntaxInCoq.vos
logic.vo logic.glob logic.v.beautified logic.required_vo: logic.v CoqIntro.vo
logic.vio: logic.v CoqIntro.vio
logic.vos logic.vok logic.required_vos: logic.v CoqIntro.vos
