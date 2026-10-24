import Collatz.MCycle111Certs47

/-!
# Certificates of the listed shapes of `data111`, chunks 188..191
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_188 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_188 = true := by
  decide +kernel

theorem certs111_189 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_189 = true := by
  decide +kernel

theorem certs111_190 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_190 = true := by
  decide +kernel

theorem certs111_191 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_191 = true := by
  decide +kernel

end Collatz
