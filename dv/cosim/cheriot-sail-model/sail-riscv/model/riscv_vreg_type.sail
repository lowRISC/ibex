/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Definitions for vector registers (V extension) */

type vreglenbits = bits(vlenmax) /* use the largest possible register length */

/* default vector register type */
type vregtype = vreglenbits

/* vector instruction types */
enum vsetop       = { VSETVLI, VSETVL }

enum vvfunct6     = { VV_VADD, VV_VSUB, VV_VMINU, VV_VMIN, VV_VMAXU, VV_VMAX, VV_VAND, VV_VOR, VV_VXOR,
  VV_VRGATHER, VV_VRGATHEREI16, VV_VSADDU, VV_VSADD, VV_VSSUBU, VV_VSSUB, VV_VSLL, VV_VSMUL,
  VV_VSRL, VV_VSRA, VV_VSSRL, VV_VSSRA }

enum vvcmpfunct6  = { VVCMP_VMSEQ, VVCMP_VMSNE, VVCMP_VMSLTU, VVCMP_VMSLT, VVCMP_VMSLEU, VVCMP_VMSLE }

enum vvmfunct6    = { VVM_VMADC, VVM_VMSBC }

enum vvmcfunct6   = { VVMC_VMADC, VVMC_VMSBC }

enum vvmsfunct6   = { VVMS_VADC, VVMS_VSBC }

enum vxmfunct6    = { VXM_VMADC, VXM_VMSBC }

enum vxmcfunct6   = { VXMC_VMADC, VXMC_VMSBC }

enum vxmsfunct6   = { VXMS_VADC, VXMS_VSBC }

enum vimfunct6    = { VIM_VMADC }

enum vimcfunct6   = { VIMC_VMADC }

enum vimsfunct6   = { VIMS_VADC }

enum vxcmpfunct6  = { VXCMP_VMSEQ, VXCMP_VMSNE, VXCMP_VMSLTU, VXCMP_VMSLT, VXCMP_VMSLEU, VXCMP_VMSLE,
  VXCMP_VMSGTU, VXCMP_VMSGT }

enum vicmpfunct6  = { VICMP_VMSEQ, VICMP_VMSNE, VICMP_VMSLEU, VICMP_VMSLE, VICMP_VMSGTU, VICMP_VMSGT }

enum nvfunct6     = { NV_VNCLIPU, NV_VNCLIP }

enum nvsfunct6    = { NVS_VNSRL, NVS_VNSRA }

enum nxfunct6     = { NX_VNCLIPU, NX_VNCLIP}

enum nxsfunct6    = { NXS_VNSRL, NXS_VNSRA }

enum mmfunct6     = { MM_VMAND, MM_VMNAND, MM_VMANDNOT, MM_VMXOR, MM_VMOR, MM_VMNOR, MM_VMORNOT, MM_VMXNOR }

enum nifunct6     = { NI_VNCLIPU, NI_VNCLIP }

enum nisfunct6    = { NIS_VNSRL, NIS_VNSRA }

enum wvvfunct6    = { WVV_VADD, WVV_VSUB, WVV_VADDU, WVV_VSUBU, WVV_VWMUL, WVV_VWMULU, WVV_VWMULSU }

enum wvfunct6     = { WV_VADD, WV_VSUB, WV_VADDU, WV_VSUBU }

enum wvxfunct6    = { WVX_VADD, WVX_VSUB, WVX_VADDU, WVX_VSUBU, WVX_VWMUL, WVX_VWMULU, WVX_VWMULSU }

enum wxfunct6     = { WX_VADD, WX_VSUB, WX_VADDU, WX_VSUBU }

enum vext2funct6  = { VEXT2_ZVF2, VEXT2_SVF2 }

enum vext4funct6  = { VEXT4_ZVF4, VEXT4_SVF4 }

enum vext8funct6  = { VEXT8_ZVF8, VEXT8_SVF8 }

enum vxfunct6     = { VX_VADD, VX_VSUB, VX_VRSUB, VX_VMINU, VX_VMIN, VX_VMAXU, VX_VMAX,
  VX_VAND, VX_VOR, VX_VXOR, VX_VSADDU, VX_VSADD, VX_VSSUBU, VX_VSSUB,
  VX_VSLL, VX_VSMUL, VX_VSRL, VX_VSRA, VX_VSSRL, VX_VSSRA }

enum vifunct6     = { VI_VADD, VI_VRSUB, VI_VAND, VI_VOR, VI_VXOR, VI_VSADDU, VI_VSADD,
  VI_VSLL, VI_VSRL, VI_VSRA, VI_VSSRL, VI_VSSRA }

enum vxsgfunct6   = { VX_VSLIDEUP, VX_VSLIDEDOWN, VX_VRGATHER }

enum visgfunct6   = { VI_VSLIDEUP, VI_VSLIDEDOWN, VI_VRGATHER }

enum mvvfunct6    = { MVV_VAADDU, MVV_VAADD, MVV_VASUBU, MVV_VASUB, MVV_VMUL, MVV_VMULH,
  MVV_VMULHU, MVV_VMULHSU, MVV_VDIVU, MVV_VDIV, MVV_VREMU, MVV_VREM }

enum mvvmafunct6  = { MVV_VMACC, MVV_VNMSAC, MVV_VMADD, MVV_VNMSUB }

enum rmvvfunct6   = { MVV_VREDSUM, MVV_VREDAND, MVV_VREDOR, MVV_VREDXOR,
  MVV_VREDMINU, MVV_VREDMIN, MVV_VREDMAXU, MVV_VREDMAX }

enum rivvfunct6   = { IVV_VWREDSUMU, IVV_VWREDSUM }

enum rfvvfunct6   = { FVV_VFREDOSUM, FVV_VFREDUSUM, FVV_VFREDMAX, FVV_VFREDMIN,
  FVV_VFWREDOSUM, FVV_VFWREDUSUM }

enum wmvvfunct6   = { WMVV_VWMACCU, WMVV_VWMACC, WMVV_VWMACCSU }

enum mvxfunct6    = { MVX_VAADDU, MVX_VAADD, MVX_VASUBU, MVX_VASUB, MVX_VSLIDE1UP, MVX_VSLIDE1DOWN,
	MVX_VMUL, MVX_VMULH, MVX_VMULHU, MVX_VMULHSU, MVX_VDIVU, MVX_VDIV, MVX_VREMU, MVX_VREM }

enum mvxmafunct6  = { MVX_VMACC, MVX_VNMSAC, MVX_VMADD, MVX_VNMSUB }

enum wmvxfunct6   = { WMVX_VWMACCU, WMVX_VWMACC, WMVX_VWMACCUS, WMVX_VWMACCSU }

enum maskfunct3   = { VV_VMERGE, VI_VMERGE, VX_VMERGE }

enum vlewidth     = { VLE8, VLE16, VLE32, VLE64 }

enum fvvfunct6    = { FVV_VADD, FVV_VSUB, FVV_VMIN, FVV_VMAX, FVV_VSGNJ, FVV_VSGNJN, FVV_VSGNJX,
  FVV_VDIV, FVV_VMUL }

enum fvvmafunct6  = { FVV_VMADD, FVV_VNMADD, FVV_VMSUB, FVV_VNMSUB, FVV_VMACC, FVV_VNMACC, FVV_VMSAC, FVV_VNMSAC }

enum fwvvfunct6   = { FWVV_VADD, FWVV_VSUB, FWVV_VMUL }

enum fwvvmafunct6 = { FWVV_VMACC, FWVV_VNMACC, FWVV_VMSAC, FWVV_VNMSAC }

enum fwvfunct6    = { FWV_VADD, FWV_VSUB }

enum fvvmfunct6   = { FVVM_VMFEQ, FVVM_VMFLE, FVVM_VMFLT, FVVM_VMFNE }

enum vfunary0     = { FV_CVT_XU_F, FV_CVT_X_F, FV_CVT_F_XU, FV_CVT_F_X, FV_CVT_RTZ_XU_F, FV_CVT_RTZ_X_F }

enum vfwunary0    = { FWV_CVT_XU_F, FWV_CVT_X_F, FWV_CVT_F_XU, FWV_CVT_F_X, FWV_CVT_F_F,
  FWV_CVT_RTZ_XU_F, FWV_CVT_RTZ_X_F }

enum vfnunary0    = { FNV_CVT_XU_F, FNV_CVT_X_F, FNV_CVT_F_XU, FNV_CVT_F_X, FNV_CVT_F_F,
  FNV_CVT_ROD_F_F, FNV_CVT_RTZ_XU_F, FNV_CVT_RTZ_X_F}

enum vfunary1     = { FVV_VSQRT, FVV_VRSQRT7, FVV_VREC7, FVV_VCLASS }

enum fvffunct6    = { VF_VADD, VF_VSUB, VF_VMIN, VF_VMAX, VF_VSGNJ, VF_VSGNJN, VF_VSGNJX,
  VF_VDIV, VF_VRDIV, VF_VMUL, VF_VRSUB, VF_VSLIDE1UP, VF_VSLIDE1DOWN }

enum fvfmafunct6  = { VF_VMADD, VF_VNMADD, VF_VMSUB, VF_VNMSUB, VF_VMACC, VF_VNMACC, VF_VMSAC, VF_VNMSAC }

enum fwvffunct6   = { FWVF_VADD, FWVF_VSUB, FWVF_VMUL }

enum fwvfmafunct6 = { FWVF_VMACC, FWVF_VNMACC, FWVF_VMSAC, FWVF_VNMSAC }

enum fwffunct6    = { FWF_VADD, FWF_VSUB }

enum fvfmfunct6   = { VFM_VMFEQ, VFM_VMFLE, VFM_VMFLT, VFM_VMFNE, VFM_VMFGT, VFM_VMFGE }

enum vmlsop       = { VLM, VSM }
