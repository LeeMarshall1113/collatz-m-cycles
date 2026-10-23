import Collatz.MCycle109Certs47

/-!
# Certificates of the listed shapes of `data109`, chunks 188..191
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_188 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_188 = true := by
  decide +kernel

theorem certs109_189 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_189 = true := by
  decide +kernel

theorem certs109_190 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_190 = true := by
  decide +kernel

theorem certs109_191 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_191 = true := by
  decide +kernel

end Collatz
