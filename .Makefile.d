Misc/Hybrid.vo Misc/Hybrid.glob Misc/Hybrid.v.beautified Misc/Hybrid.required_vo: Misc/Hybrid.v 
Misc/Hybrid.vio: Misc/Hybrid.v 
Misc/Hybrid.vos Misc/Hybrid.vok Misc/Hybrid.required_vos: Misc/Hybrid.v 
Misc/Permutations.vo Misc/Permutations.glob Misc/Permutations.v.beautified Misc/Permutations.required_vo: Misc/Permutations.v 
Misc/Permutations.vio: Misc/Permutations.v 
Misc/Permutations.vos Misc/Permutations.vok Misc/Permutations.required_vos: Misc/Permutations.v 
Misc/UtilsTactics.vo Misc/UtilsTactics.glob Misc/UtilsTactics.v.beautified Misc/UtilsTactics.required_vo: Misc/UtilsTactics.v Misc/Permutations.vo
Misc/UtilsTactics.vio: Misc/UtilsTactics.v Misc/Permutations.vio
Misc/UtilsTactics.vos Misc/UtilsTactics.vok Misc/UtilsTactics.required_vos: Misc/UtilsTactics.v Misc/Permutations.vos
Misc/Utils.vo Misc/Utils.glob Misc/Utils.v.beautified Misc/Utils.required_vo: Misc/Utils.v Misc/UtilsTactics.vo
Misc/Utils.vio: Misc/Utils.v Misc/UtilsTactics.vio
Misc/Utils.vos Misc/Utils.vok Misc/Utils.required_vos: Misc/Utils.v Misc/UtilsTactics.vos
SL/Syntax.vo SL/Syntax.glob SL/Syntax.v.beautified SL/Syntax.required_vo: SL/Syntax.v Misc/Utils.vo Misc/Permutations.vo Misc/Hybrid.vo
SL/Syntax.vio: SL/Syntax.v Misc/Utils.vio Misc/Permutations.vio Misc/Hybrid.vio
SL/Syntax.vos SL/Syntax.vok SL/Syntax.required_vos: SL/Syntax.v Misc/Utils.vos Misc/Permutations.vos Misc/Hybrid.vos
SL/Sequent.vo SL/Sequent.glob SL/Sequent.v.beautified SL/Sequent.required_vo: SL/Sequent.v Misc/Utils.vo SL/Syntax.vo
SL/Sequent.vio: SL/Sequent.v Misc/Utils.vio SL/Syntax.vio
SL/Sequent.vos SL/Sequent.vok SL/Sequent.required_vos: SL/Sequent.v Misc/Utils.vos SL/Syntax.vos
SL/FLLTacticsPre.vo SL/FLLTacticsPre.glob SL/FLLTacticsPre.v.beautified SL/FLLTacticsPre.required_vo: SL/FLLTacticsPre.v Misc/Utils.vo SL/Sequent.vo Misc/Permutations.vo
SL/FLLTacticsPre.vio: SL/FLLTacticsPre.v Misc/Utils.vio SL/Sequent.vio Misc/Permutations.vio
SL/FLLTacticsPre.vos SL/FLLTacticsPre.vok SL/FLLTacticsPre.required_vos: SL/FLLTacticsPre.v Misc/Utils.vos SL/Sequent.vos Misc/Permutations.vos
SL/StructuralRules.vo SL/StructuralRules.glob SL/StructuralRules.v.beautified SL/StructuralRules.required_vo: SL/StructuralRules.v Misc/Utils.vo Misc/Permutations.vo SL/FLLTacticsPre.vo
SL/StructuralRules.vio: SL/StructuralRules.v Misc/Utils.vio Misc/Permutations.vio SL/FLLTacticsPre.vio
SL/StructuralRules.vos SL/StructuralRules.vok SL/StructuralRules.required_vos: SL/StructuralRules.v Misc/Utils.vos Misc/Permutations.vos SL/FLLTacticsPre.vos
SL/FLLTactics.vo SL/FLLTactics.glob SL/FLLTactics.v.beautified SL/FLLTactics.required_vo: SL/FLLTactics.v SL/StructuralRules.vo SL/FLLTacticsPre.vo
SL/FLLTactics.vio: SL/FLLTactics.v SL/StructuralRules.vio SL/FLLTacticsPre.vio
SL/FLLTactics.vos SL/FLLTactics.vok SL/FLLTactics.required_vos: SL/FLLTactics.v SL/StructuralRules.vos SL/FLLTacticsPre.vos
SL/InvNegativePhase.vo SL/InvNegativePhase.glob SL/InvNegativePhase.v.beautified SL/InvNegativePhase.required_vo: SL/InvNegativePhase.v Misc/Hybrid.vo SL/FLLTactics.vo Misc/Permutations.vo
SL/InvNegativePhase.vio: SL/InvNegativePhase.v Misc/Hybrid.vio SL/FLLTactics.vio Misc/Permutations.vio
SL/InvNegativePhase.vos SL/InvNegativePhase.vok SL/InvNegativePhase.required_vos: SL/InvNegativePhase.v Misc/Hybrid.vos SL/FLLTactics.vos Misc/Permutations.vos
SL/InvPositivePhase.vo SL/InvPositivePhase.glob SL/InvPositivePhase.v.beautified SL/InvPositivePhase.required_vo: SL/InvPositivePhase.v Misc/Hybrid.vo SL/FLLTactics.vo Misc/Permutations.vo SL/InvNegativePhase.vo
SL/InvPositivePhase.vio: SL/InvPositivePhase.v Misc/Hybrid.vio SL/FLLTactics.vio Misc/Permutations.vio SL/InvNegativePhase.vio
SL/InvPositivePhase.vos SL/InvPositivePhase.vok SL/InvPositivePhase.required_vos: SL/InvPositivePhase.v Misc/Hybrid.vos SL/FLLTactics.vos Misc/Permutations.vos SL/InvNegativePhase.vos
SL/CutElimination.vo SL/CutElimination.glob SL/CutElimination.v.beautified SL/CutElimination.required_vo: SL/CutElimination.v Misc/Hybrid.vo SL/FLLTactics.vo Misc/Permutations.vo SL/InvPositivePhase.vo
SL/CutElimination.vio: SL/CutElimination.v Misc/Hybrid.vio SL/FLLTactics.vio Misc/Permutations.vio SL/InvPositivePhase.vio
SL/CutElimination.vos SL/CutElimination.vok SL/CutElimination.required_vos: SL/CutElimination.v Misc/Hybrid.vos SL/FLLTactics.vos Misc/Permutations.vos SL/InvPositivePhase.vos
OL/CutCoherence/OLSyntax.vo OL/CutCoherence/OLSyntax.glob OL/CutCoherence/OLSyntax.v.beautified OL/CutCoherence/OLSyntax.required_vo: OL/CutCoherence/OLSyntax.v Misc/Hybrid.vo SL/FLLTactics.vo
OL/CutCoherence/OLSyntax.vio: OL/CutCoherence/OLSyntax.v Misc/Hybrid.vio SL/FLLTactics.vio
OL/CutCoherence/OLSyntax.vos OL/CutCoherence/OLSyntax.vok OL/CutCoherence/OLSyntax.required_vos: OL/CutCoherence/OLSyntax.v Misc/Hybrid.vos SL/FLLTactics.vos
