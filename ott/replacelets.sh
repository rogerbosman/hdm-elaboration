#!/bin/bash
cp ~/hdm/ott/HdmDefs.v ~/hdm/ott/HdmDefsSubst.v
perl -0777 -e '$out = <>; $in = <>; $_ = <>; s/\Q$out\E/$in/g; print ' ~/hdm/ott/DecLet-out.v ~/hdm/ott/DecLet-in.v ~/hdm/ott/HdmDefsSubst.v > ~/hdm/ott/HdmDefsSubstTmp.v ;
cp ~/hdm/ott/HdmDefsSubstTmp.v ~/hdm/ott/HdmDefsSubst.v
perl -0777 -e '$out = <>; $in = <>; $_ = <>; s/\Q$out\E/$in/g; print ' ~/hdm/ott/InfLet-out.v ~/hdm/ott/InfLet-in.v ~/hdm/ott/HdmDefsSubst.v > ~/hdm/ott/HdmDefsSubstTmp.v
cp ~/hdm/ott/HdmDefsSubstTmp.v ~/hdm/ott/HdmDefsSubst.v
perl -0777 -e '$out = <>; $in = <>; $_ = <>; s/\Q$out\E/$in/g; print ' ~/hdm/ott/DecAbs-out.v ~/hdm/ott/DecAbs-in.v ~/hdm/ott/HdmDefsSubst.v > ~/hdm/ott/HdmDefsSubstTmp.v ;
cp ~/hdm/ott/HdmDefsSubstTmp.v ~/hdm/ott/HdmDefsSubst.v
perl -0777 -e '$out = <>; $in = <>; $_ = <>; s/\Q$out\E/$in/g; print ' ~/hdm/ott/InfAbs-out.v ~/hdm/ott/InfAbs-in.v ~/hdm/ott/HdmDefsSubst.v > ~/hdm/ott/HdmDefsSubstTmp.v
cp ~/hdm/ott/HdmDefsSubstTmp.v ~/hdm/ott/HdmDefsSubst.v

rm ~/hdm/ott/HdmDefsSubstTmp.v
