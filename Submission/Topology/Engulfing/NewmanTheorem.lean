import Submission.Topology.Engulfing.NewmanPreparedAttachment
import Submission.Topology.Engulfing.LocalObstacleInnerGeometry
import Submission.Topology.Engulfing.LocalObstacleInnerModel
import Submission.Topology.Engulfing.NewmanLocalAttachment
import Submission.Topology.Engulfing.NewmanDimensionInduction

/-!
# Relative topological engulfing

Joint general position prepares the local membrane attachment. Its finite
inner iteration uses the preceding relative dimension, closing the dimension
induction with no additional engulfing hypothesis.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Geometry Topology
open scoped ContinuousMap

variable {M : Type*} [MetricSpace M] {n p q : ℕ}

theorem localSkeletalAttachmentAt_of_relative
    (hqp : q ≤ p) (hlower : RelativeNewmanAt M n p q) :
    LocalSkeletalAttachmentAt M n p q := by
  intro E _ _ _ _ K L hK hLK hd g X U hX hU hp hconn hfixed hdata
    b C V B hC hCpoly hCp hV hVq ha hVcore havoid hcover ε hε
  obtain ⟨P⟩ := exists_local_obstacle_attachment_preparation K L hK hLK hd
    (by omega : p + 1 ≤ n) g hU b C hC hCpoly hCp V B hV hVq ha hVcore hcover
    (half_pos hε)
  let S := P.chartSetup
  let m := P.model
  let geometry := S.innerGeometry m P.active P.active_faces P.active_space havoid
  obtain ⟨inner⟩ := S.exists_innerModel m P.covered P.active P.covered_faces
    P.active_faces P.active_space geometry rfl
  obtain ⟨g', G, hfix, hnear, hnew, hcompact⟩ :=
    P.exists_conclusion inner hlower hqp hX hU hp hconn hdata hfixed (half_pos hε)
  exact ⟨g', G, hfix, fun x => by simpa only [add_halves] using hnear x, hnew, hcompact⟩

/-- Newman's relative engulfing theorem, proved by induction on the uncovered
target dimension. The codimension and connectivity requirements are carried
by each concrete problem. -/
theorem relativeNewmanAt (M : Type*) [MetricSpace M] (n p q : ℕ) :
    RelativeNewmanAt M n p q := by
  apply relativeNewmanAt_of_singleSimplex_steps_le
  intro k hkp hrelative
  exact singleSimplexNewmanAt_of_localAttachment
    (localSkeletalAttachmentAt_of_relative hkp hrelative)

end PoincareHighDim.Engulfing
