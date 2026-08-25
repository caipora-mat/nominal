-- Aggregator for the nominal unification subsystem.  Importing `Mgu` transitively
-- pulls the whole chain: Mgu → Completeness → Properties → Algorithm → Helpers,
-- and Mgu → SimSubst → Basic.  So this single import covers every module.
import Nominal.Syntax.Unification.Mgu
