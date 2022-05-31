Misc/Hybrid.vo Misc/Hybrid.glob Misc/Hybrid.v.beautified Misc/Hybrid.required_vo: Misc/Hybrid.v 
Misc/Hybrid.vio: Misc/Hybrid.v 
Misc/Hybrid.vos Misc/Hybrid.vok Misc/Hybrid.required_vos: Misc/Hybrid.v 
Misc/Database.vo Misc/Database.glob Misc/Database.v.beautified Misc/Database.required_vo: Misc/Database.v 
Misc/Database.vio: Misc/Database.v 
Misc/Database.vos Misc/Database.vok Misc/Database.required_vos: Misc/Database.v 
Misc/Permutations.vo Misc/Permutations.glob Misc/Permutations.v.beautified Misc/Permutations.required_vo: Misc/Permutations.v 
Misc/Permutations.vio: Misc/Permutations.v 
Misc/Permutations.vos Misc/Permutations.vok Misc/Permutations.required_vos: Misc/Permutations.v 
Misc/UtilsTactics.vo Misc/UtilsTactics.glob Misc/UtilsTactics.v.beautified Misc/UtilsTactics.required_vo: Misc/UtilsTactics.v Misc/Permutations.vo Misc/Utils.vo
Misc/UtilsTactics.vio: Misc/UtilsTactics.v Misc/Permutations.vio Misc/Utils.vio
Misc/UtilsTactics.vos Misc/UtilsTactics.vok Misc/UtilsTactics.required_vos: Misc/UtilsTactics.v Misc/Permutations.vos Misc/Utils.vos
Misc/Utils.vo Misc/Utils.glob Misc/Utils.v.beautified Misc/Utils.required_vo: Misc/Utils.v 
Misc/Utils.vio: Misc/Utils.v 
Misc/Utils.vos Misc/Utils.vok Misc/Utils.required_vos: Misc/Utils.v 
SL/Signature.vo SL/Signature.glob SL/Signature.v.beautified SL/Signature.required_vo: SL/Signature.v Misc/UtilsTactics.vo Misc/Database.vo
SL/Signature.vio: SL/Signature.v Misc/UtilsTactics.vio Misc/Database.vio
SL/Signature.vos SL/Signature.vok SL/Signature.required_vos: SL/Signature.v Misc/UtilsTactics.vos Misc/Database.vos
SL/Syntax.vo SL/Syntax.glob SL/Syntax.v.beautified SL/Syntax.required_vo: SL/Syntax.v Misc/UtilsTactics.vo Misc/Permutations.vo Misc/Hybrid.vo Misc/Database.vo SL/Signature.vo
SL/Syntax.vio: SL/Syntax.v Misc/UtilsTactics.vio Misc/Permutations.vio Misc/Hybrid.vio Misc/Database.vio SL/Signature.vio
SL/Syntax.vos SL/Syntax.vok SL/Syntax.required_vos: SL/Syntax.v Misc/UtilsTactics.vos Misc/Permutations.vos Misc/Hybrid.vos Misc/Database.vos SL/Signature.vos
SL/Locations.vo SL/Locations.glob SL/Locations.v.beautified SL/Locations.required_vo: SL/Locations.v SL/Syntax.vo
SL/Locations.vio: SL/Locations.v SL/Syntax.vio
SL/Locations.vos SL/Locations.vok SL/Locations.required_vos: SL/Locations.v SL/Syntax.vos
SL/Sequent.vo SL/Sequent.glob SL/Sequent.v.beautified SL/Sequent.required_vo: SL/Sequent.v Misc/Utils.vo SL/Locations.vo
SL/Sequent.vio: SL/Sequent.v Misc/Utils.vio SL/Locations.vio
SL/Sequent.vos SL/Sequent.vok SL/Sequent.required_vos: SL/Sequent.v Misc/Utils.vos SL/Locations.vos
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
SL/FLLReasoning.vo SL/FLLReasoning.glob SL/FLLReasoning.v.beautified SL/FLLReasoning.required_vo: SL/FLLReasoning.v SL/FLLTactics.vo SL/CutElimination.vo
SL/FLLReasoning.vio: SL/FLLReasoning.v SL/FLLTactics.vio SL/CutElimination.vio
SL/FLLReasoning.vos SL/FLLReasoning.vok SL/FLLReasoning.required_vos: SL/FLLReasoning.v SL/FLLTactics.vos SL/CutElimination.vos
OL/CutCoherence/OLSyntax.vo OL/CutCoherence/OLSyntax.glob OL/CutCoherence/OLSyntax.v.beautified OL/CutCoherence/OLSyntax.required_vo: OL/CutCoherence/OLSyntax.v Misc/Hybrid.vo SL/FLLTactics.vo
OL/CutCoherence/OLSyntax.vio: OL/CutCoherence/OLSyntax.v Misc/Hybrid.vio SL/FLLTactics.vio
OL/CutCoherence/OLSyntax.vos OL/CutCoherence/OLSyntax.vok OL/CutCoherence/OLSyntax.required_vos: OL/CutCoherence/OLSyntax.v Misc/Hybrid.vos SL/FLLTactics.vos
OL/CutCoherence/OLDefinitions.vo OL/CutCoherence/OLDefinitions.glob OL/CutCoherence/OLDefinitions.v.beautified OL/CutCoherence/OLDefinitions.required_vo: OL/CutCoherence/OLDefinitions.v Misc/Hybrid.vo OL/CutCoherence/OLSyntax.vo SL/CutElimination.vo
OL/CutCoherence/OLDefinitions.vio: OL/CutCoherence/OLDefinitions.v Misc/Hybrid.vio OL/CutCoherence/OLSyntax.vio SL/CutElimination.vio
OL/CutCoherence/OLDefinitions.vos OL/CutCoherence/OLDefinitions.vok OL/CutCoherence/OLDefinitions.required_vos: OL/CutCoherence/OLDefinitions.v Misc/Hybrid.vos OL/CutCoherence/OLSyntax.vos SL/CutElimination.vos
OL/CutCoherence/OLTactics.vo OL/CutCoherence/OLTactics.glob OL/CutCoherence/OLTactics.v.beautified OL/CutCoherence/OLTactics.required_vo: OL/CutCoherence/OLTactics.v Misc/Hybrid.vo SL/FLLTactics.vo OL/CutCoherence/OLSyntax.vo OL/CutCoherence/OLDefinitions.vo
OL/CutCoherence/OLTactics.vio: OL/CutCoherence/OLTactics.v Misc/Hybrid.vio SL/FLLTactics.vio OL/CutCoherence/OLSyntax.vio OL/CutCoherence/OLDefinitions.vio
OL/CutCoherence/OLTactics.vos OL/CutCoherence/OLTactics.vok OL/CutCoherence/OLTactics.required_vos: OL/CutCoherence/OLTactics.v Misc/Hybrid.vos SL/FLLTactics.vos OL/CutCoherence/OLSyntax.vos OL/CutCoherence/OLDefinitions.vos
OL/CutCoherence/OLPosNeg.vo OL/CutCoherence/OLPosNeg.glob OL/CutCoherence/OLPosNeg.v.beautified OL/CutCoherence/OLPosNeg.required_vo: OL/CutCoherence/OLPosNeg.v OL/CutCoherence/OLTactics.vo OL/CutCoherence/OLDefinitions.vo
OL/CutCoherence/OLPosNeg.vio: OL/CutCoherence/OLPosNeg.v OL/CutCoherence/OLTactics.vio OL/CutCoherence/OLDefinitions.vio
OL/CutCoherence/OLPosNeg.vos OL/CutCoherence/OLPosNeg.vok OL/CutCoherence/OLPosNeg.required_vos: OL/CutCoherence/OLPosNeg.v OL/CutCoherence/OLTactics.vos OL/CutCoherence/OLDefinitions.vos
OL/CutCoherence/Bipoles.vo OL/CutCoherence/Bipoles.glob OL/CutCoherence/Bipoles.v.beautified OL/CutCoherence/Bipoles.required_vo: OL/CutCoherence/Bipoles.v OL/CutCoherence/OLTactics.vo OL/CutCoherence/OLPosNeg.vo
OL/CutCoherence/Bipoles.vio: OL/CutCoherence/Bipoles.v OL/CutCoherence/OLTactics.vio OL/CutCoherence/OLPosNeg.vio
OL/CutCoherence/Bipoles.vos OL/CutCoherence/Bipoles.vok OL/CutCoherence/Bipoles.required_vos: OL/CutCoherence/Bipoles.v OL/CutCoherence/OLTactics.vos OL/CutCoherence/OLPosNeg.vos
OL/CutCoherence/KT4/KT4Bipoles.vo OL/CutCoherence/KT4/KT4Bipoles.glob OL/CutCoherence/KT4/KT4Bipoles.v.beautified OL/CutCoherence/KT4/KT4Bipoles.required_vo: OL/CutCoherence/KT4/KT4Bipoles.v Misc/Hybrid.vo OL/CutCoherence/Bipoles.vo
OL/CutCoherence/KT4/KT4Bipoles.vio: OL/CutCoherence/KT4/KT4Bipoles.v Misc/Hybrid.vio OL/CutCoherence/Bipoles.vio
OL/CutCoherence/KT4/KT4Bipoles.vos OL/CutCoherence/KT4/KT4Bipoles.vok OL/CutCoherence/KT4/KT4Bipoles.required_vos: OL/CutCoherence/KT4/KT4Bipoles.v Misc/Hybrid.vos OL/CutCoherence/Bipoles.vos
