import Collatz.MCycle111Certs52

/-!
# Certificates of the listed shapes of `data111`, chunks 208..211
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_208 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_208 = true := by
  decide +kernel

theorem certs111_209 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_209 = true := by
  decide +kernel

theorem certs111_210 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_210 = true := by
  decide +kernel

theorem certs111_211 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_211 = true := by
  decide +kernel

end Collatz
