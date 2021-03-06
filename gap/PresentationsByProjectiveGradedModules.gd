#############################################################################
##
## PresentationsByProjectiveGradedModules
##
## Copyright 2019,  Martin Bies,       ULB Brussels
##
#! @Chapter The CAP category of graded module presentations for CAP
##
#############################################################################



######################################################################
##
#! @Section The GAP categories for graded module presentations for CAP
##
######################################################################

#! @Description
#! The GAP category of graded left and right module presentations.
#! @Arguments object
DeclareCategory( "IsGradedLeftOrRightModulePresentationForCAP",
                 IsCAPPresentationCategoryObject );

#! @Description
#! The GAP category of objects in the presentation category over the category of projective graded left modules.
#! @Arguments object
DeclareCategory( "IsGradedLeftModulePresentationForCAP",
                 IsGradedLeftOrRightModulePresentationForCAP );

#! @Description
#! The GAP category of objects in the presentation category over the category of projective graded right modules.
#! @Arguments object
DeclareCategory( "IsGradedRightModulePresentationForCAP",
                 IsGradedLeftOrRightModulePresentationForCAP );



###############################################################################
##
#! @Section The GAP categories for graded module presentation morphisms for CAP
##
###############################################################################

#! @Description
#! The GAP category of left or right module presentation morphisms
#! @Arguments object
DeclareCategory( "IsGradedLeftOrRightModulePresentationMorphismForCAP",
                 IsCAPPresentationCategoryMorphism );

#! @Description
#! The GAP category of morphisms in the presentation category over the category of projective graded left modules.
#! @Arguments object
DeclareCategory( "IsGradedLeftModulePresentationMorphismForCAP",
                 IsGradedLeftOrRightModulePresentationMorphismForCAP );

#! @Description
#! The GAP category of morphisms in the presentation category over the category of projective graded right modules.
#! @Arguments object
DeclareCategory( "IsGradedRightModulePresentationMorphismForCAP",
                 IsGradedLeftOrRightModulePresentationMorphismForCAP );



######################################
##
#! @Section CAP categories
##
######################################

#! @Description
#! Given a graded ring <A>S</A>, one can consider the category of f.p. graded left $S$-modules, which is 
#! captured by this attribute.
#! @Returns a CapCategory
#! @Arguments S
DeclareAttribute( "SfpgrmodLeft",
                 IsHomalgGradedRing );

#! @Description
#! Given a graded ring <A>S</A>, one can consider the category of f.p. graded right $S$-modules, which is 
#! captured by this attribute.
#! @Returns a CapCategory
#! @Arguments S
DeclareAttribute( "SfpgrmodRight",
                 IsHomalgGradedRing ); 



##############################################
##
## @Section Hom-Embedding
##
##############################################

# A method specialised to graded module presentation is installed to compute Hom-embeddings in this context. They perform faster
# than the method installed by the presentation category.