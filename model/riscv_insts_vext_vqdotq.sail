/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ******************************************************************************* */
/* This file implements the vector Dot-Product Extension: Zvqdotq                  */
/*********************************************************************************/

/* ******************************* OPFVV (VVTYPE) ******************************** */
union clause ast = FVVTYPE : (fvvfunct6, bits(1), vregidx, vregidx, vregidx)

mapping encdec_fvvfunct6 : fvvfunct6 <-> bits(6) = {
  FVV_VQDOT       <-> 0b101100,
  FVV_VQDOTU      <-> 0b101000,
  FVV_VQDOTSU     <-> 0b101010
}

mapping clause encdec = FVVTYPE(funct6, vm, vs2, vs1, vd)                                                       if extensionEnabled(Ext_V)
  <-> encdec_fvvfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b001 @ encdec_vreg(vd) @ 0b1010111 if extensionEnabled(Ext_V)

function clause execute(FVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  // Check if SEW is not equal to 32
  if SEW != 32 then {
    // Only SEW = 32 is supported
    print("SEW is not equal to 32");
    return RETIRE_FAIL
  }

  let 'n = num_elem;
  let 'm = SEW; // 32

  let vm_val  : bits('n)            = read_vmask(num_elem, vm, zvreg);
  // let vs1_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  // let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  // let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);

  let (initial_result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);
  var result = initial_result;

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] == bitone then {
      let {a0 @ a1 @ a2 @ a3} : bits(4 * 8) = get_velem(vs2, SEW, i);
      let {b0 @ b1 @ b2 @ b3} : bits(4 * 8) = get_velem(vs1, SEW, i);
      let acc : bits(SEW) = get_velem(vd, SEW, i);

      // Conditionally sign extend based on the instruction type
      if funct6 == FVV_VQDOT or funct6 == FVV_VQDOTSU then {
        a0 = sign_extend(a0);
        a1 = sign_extend(a1);
        a2 = sign_extend(a2);
        a3 = sign_extend(a3);
      }
      if funct6 == FVV_VQDOT or funct6 == FVV_VQDOTUS then {
        b0 = sign_extend(b0);
        b1 = sign_extend(b1);
        b2 = sign_extend(b2);
        b3 = sign_extend(b3);
      }

      let res : bits(SEW) = a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + acc;
      set_velem(result, i, res);
    }
  }

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}

  mapping fvvtype_mnemonic : fvvfunct6 <-> string = {
    FVV_VQDOT       <-> "vqdot.vv",
    FVV_VQDOTU      <-> "vqdotu.vv",
    FVV_VQDOTSU     <-> "vqdotsu.vv"
   }

mapping clause assembly = FVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> fvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ******************************* OPIVX (VXTYPE) ******************************** */

union clause ast = FVVTYPE : (fvvfunct6, bits(1), vregidx, vregidx, vregidx)

mapping encdec_fvvfunct6 : fvvfunct6 <-> bits(6) = {
  FVX_VQDOT       <-> 0b101100,
  FVX_VQDOTU      <-> 0b101000,
  FVX_VQDOTSU     <-> 0b101010,
  FVX_VQDOTUS     <-> 0b101110
}

mapping clause encdec = FVVTYPE(funct6, vm, vs2, vs1, vd)                                                       if extensionEnabled(Ext_V)
  <-> encdec_fvvfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b001 @ encdec_vreg(vd) @ 0b1010111 if extensionEnabled(Ext_V)

function clause execute(FVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  // Check if SEW is not equal to 32
  if SEW != 32 then {
    // Only SEW = 32 is supported
    print("SEW is not equal to 32");
    return RETIRE_FAIL
  }

  let 'n = num_elem;
  let 'm = SEW; // 32

  let vm_val  : bits('n)            = read_vmask(num_elem, vm, zvreg);
//  let vs1_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
//  let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
//  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);

  let (initial_result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);
  var result = initial_result;

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] == bitone then {
      let {a0 @ a1 @ a2 @ a3} : bits(4 * 8) = get_velem(vs2, SEW, i);
//      let {b0 @ b1 @ b2 @ b3} : bits(4 * 8) = get_velem(vs1, SEW, i);
// Need to get lowest byte of X(RS1) and duplicate 4 Times
//
// You are here <<<<<<<<<
//
      let acc : bits(SEW) = get_velem(vd_val, i);

      // Conditionally sign extend based on the instruction type
      if funct6 == FVV_VQDOT or funct6 == FVV_VQDOTSU then {
        a0 = sign_extend(a0);
        a1 = sign_extend(a1);
        a2 = sign_extend(a2);
        a3 = sign_extend(a3);
      }
      if funct6 == FVV_VQDOT or funct6 == FVV_VQDOTUS then {
        b0 = sign_extend(b0);
        b1 = sign_extend(b1);
        b2 = sign_extend(b2);
        b3 = sign_extend(b3);
      }

      let res : bits(SEW) = a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + acc;
      set_velem(result, i, res);
    }
  }

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}


mapping clause encdec = FVVTYPE(funct6, vm, vs2, vs1, vd)                                                       if extensionEnabled(Ext_V)
  <-> encdec_fvvfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b001 @ encdec_vreg(vd) @ 0b1010111 if extensionEnabled(Ext_V)
  mapping fvxtype_mnemonic : fvvfunct6 <-> string = {
    FVX_VQDOT       <-> "vqdot.vx",
    FVX_VQDOTU      <-> "vqdotu.vx",
    FVX_VQDOTSU     <-> "vqdotsu.vx",
    FVX_VQDOTUS     <-> "vqdotus.vx"
   }

   mapping clause assembly = VXTYPE(funct6, vm, vs2, rs1, vd)
  <-> vxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)
