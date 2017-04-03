####################################################################################
##
## GradedModulePresentationsForCAP
##
## Copyright 2016,  Martin Bies,       ITP Heidelberg
##
## Chapter Tools
##
####################################################################################



####################################################################################
##
#! @Section Saturation
##
####################################################################################

# Saturate the first object with respect to the second object (if the second can be viewed as ideal)
InstallMethod( Saturate,
               "Saturate the first object with respect to the second",
               [ IsGradedLeftModulePresentationForCAP, IsGradedLeftIdealForCAP ],
  function( module, ideal )
    local ideal_embedding, homalg_graded_ring, homalg_graded_ring_module, module_saturated, buffer_mapping;

    # first check that the second object is indeed an ideal
    ideal_embedding := EmbeddingInSuperObjectForCAP( ideal );
    homalg_graded_ring := HomalgGradedRing( ideal );
    if not IsIdenticalObj( UnderlyingHomalgGradedRing( UnderlyingMorphism( module ) ), homalg_graded_ring ) then

      Error( "The module and ideal must be defined over the same homalg_graded_ring" );
      return;

    fi;

    # save the image of the ideal_embedding
    homalg_graded_ring_module := Range( ideal_embedding );

    # now compute the saturation
    module_saturated := module;
    #buffer_mapping := ByASmallerPresentation(
    #                        InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

    buffer_mapping := InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) );

    Error( "before iso" );

    while not IsIsomorphism( buffer_mapping ) do

      module_saturated := ByASmallerPresentation( 
                                  InternalHomOnObjects( homalg_graded_ring_module ,
                                                        InternalHomOnObjects( PresentationForCAP( ideal ), module_saturated ) 
                                                       ) );
      buffer_mapping := ByASmallerPresentation( 
                                  InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

      Error( "Before iso" );

    od;

    # finally return the satured module
    return module_saturated;

end );

InstallMethod( Saturate,
               "Saturate the first object with respect to the second",
               [ IsGradedLeftSubmoduleForCAP, IsGradedLeftIdealForCAP ],
  function( submodule, ideal )

    return Saturate( PresentationForCAP( submodule ), ideal );

end );

# Saturate the first object with respect to the second object (if the second can be viewed as ideal)
InstallMethod( Saturate,
               "Saturate the first object with respect to the second",
               [ IsGradedRightModulePresentationForCAP, IsGradedRightIdealForCAP ],
  function( module, ideal )
    local ideal_embedding, homalg_graded_ring, homalg_graded_ring_module, module_saturated, buffer_mapping;

    # first check that the second object is indeed an ideal
    ideal_embedding := EmbeddingInSuperObjectForCAP( ideal );
    homalg_graded_ring := HomalgGradedRing( ideal );
    if not IsIdenticalObj( UnderlyingHomalgGradedRing( UnderlyingMorphism( module ) ), homalg_graded_ring ) then

      Error( "The module and ideal must be defined over the same homalg_graded_ring" );
      return;

    fi;

    # save the image of the ideal_embedding
    homalg_graded_ring_module := Range( ideal_embedding );

    # now compute the saturation
    module_saturated := module;
    buffer_mapping := ByASmallerPresentation(
                             InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

    while not IsIsomorphism( buffer_mapping ) do

      module_saturated := ByASmallerPresentation(
                                  InternalHomOnObjects( homalg_graded_ring_module ,
                                                InternalHomOnObjects( PresentationForCAP( ideal ), module_saturated ) 
                                               ) );
      buffer_mapping := ByASmallerPresentation(
                                  InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

    od;

    # finally return the satured module
    return module_saturated;

end );

InstallMethod( Saturate,
               "Saturate the first object with respect to the second",
               [ IsGradedRightSubmoduleForCAP, IsGradedRightIdealForCAP ],
  function( submodule, ideal )

    return Saturate( PresentationForCAP( submodule ), ideal );

end );

# Compute the embedding of the first object into its saturation with respect to the given ideal
InstallMethod( EmbeddingInSaturationOfGradedModulePresentation,
               "Compute embedding of first object into its saturation with respect to the second object",
               [ IsGradedLeftModulePresentationForCAP, IsGradedLeftIdealForCAP ],
  function( module, ideal )

    local ideal_embedding, homalg_graded_ring, homalg_graded_ring_module, module_saturated, embedding, buffer_mapping;

    # first check that the second object is indeed an ideal
    ideal_embedding := EmbeddingInSuperObjectForCAP( ideal );
    homalg_graded_ring := HomalgGradedRing( ideal );
    if not IsIdenticalObj( UnderlyingHomalgGradedRing( UnderlyingMorphism( module ) ), homalg_graded_ring ) then

      Error( "The module and ideal need to be defined over the same homalg_graded_ring" );
      return;

    fi;

    # save the image of the ideal_embedding
    homalg_graded_ring_module := Range( ideal_embedding );

    # now compute the saturation    
    embedding := IdentityMorphism( module );
    module_saturated := Range( embedding );

    buffer_mapping := ByASmallerPresentation(
                               InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

    while not IsIsomorphism( buffer_mapping ) do

      embedding := PreCompose( embedding, 
                               InternalHomOnMorphisms( IdentityMorphism( homalg_graded_ring_module ), buffer_mapping ) );

      module_saturated := Range( embedding );

      buffer_mapping := ByASmallerPresentation(
                               InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

    od;

    # finally return the satured module
    return embedding;

end );

InstallMethod( EmbeddingInSaturationOfGradedModulePresentation,
               "Compute embedding of first object into its saturation with respect to the second object",
               [ IsGradedLeftSubmoduleForCAP, IsGradedLeftIdealForCAP ],
  function( submodule, ideal )

    return EmbeddingInSaturationOfGradedModulePresentation( PresentationForCAP( submodule ), ideal );

end );

# Compute the embedding of the first object into its saturation with respect to the given ideal
InstallMethod( EmbeddingInSaturationOfGradedModulePresentation,
               "Compute embedding of first object into its saturation with respect to the second object",
               [ IsGradedRightModulePresentationForCAP, IsGradedRightIdealForCAP ],
  function( module, ideal )

    local ideal_embedding, homalg_graded_ring, homalg_graded_ring_module, module_saturated, embedding, buffer_mapping;

    # check that the module and the ideal are defined over the same ring
    ideal_embedding := EmbeddingInSuperObjectForCAP( ideal );
    homalg_graded_ring := UnderlyingHomalgGradedRing( UnderlyingMorphism( ideal ) );
    if not IsIdenticalObj( UnderlyingHomalgGradedRing( UnderlyingMorphism( module ) ), homalg_graded_ring ) then

      Error( "The module and ideal need to be defined over the same homalg_graded_ring" );
      return;

    fi;

    # save the image of the ideal_embedding
    homalg_graded_ring_module := Range( ideal_embedding );

    # now compute the saturation
    embedding := IdentityMorphism( module );
    module_saturated := Range( embedding );

    buffer_mapping := ByASmallerPresentation(
                           InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

    while not IsIsomorphism( buffer_mapping ) do

      embedding := PreCompose( embedding, 
                               InternalHomOnMorphisms( IdentityMorphism( homalg_graded_ring_module ), buffer_mapping ) );

      module_saturated := Range( embedding );

      buffer_mapping := ByASmallerPresentation( InternalHomOnMorphisms( ideal_embedding, IdentityMorphism( module_saturated ) ) );

    od;

    # finally return the satured module
    return embedding;

end );

InstallMethod( EmbeddingInSaturationOfGradedModulePresentation,
               "Compute embedding of first object into its saturation with respect to the second object",
               [ IsGradedRightSubmoduleForCAP, IsGradedRightIdealForCAP ],
  function( submodule, ideal )

    return EmbeddingInSaturationOfGradedModulePresentation( PresentationForCAP( submodule ), ideal );

end );



####################################################################################
##
##  Section Embeddings in projective modules
##
####################################################################################

# represent ideal of graded ring as graded left-presentation
InstallMethod( EmbeddingInProjectiveObject,
               "for a graded module presentation",
               [ IsGradedLeftOrRightModulePresentationForCAP ],
  function( presentation_object )
    local cokernel_projection, range_object;

    # compute the cokernel projection of the presentation_object
    cokernel_projection := CokernelProjection( UnderlyingMorphism( presentation_object ) );

    # we are thus looking at the following diagram:
    #
    # presentation_object_source ----- zero_morphism -------------- 0
    #            |                                                  |
    # underlying_morphism                                    zero_morphism
    #            |                                                  |
    #            v                                                  v
    # presentation_object_range ---- cokernel_projection ----> cokernel_object
    #
    # the right column is the projective_module that we embed the left column into

    range_object := CAPPresentationCategoryObject( 
                         ZeroMorphism( ZeroObject( CapCategory( cokernel_projection ) ), Range( cokernel_projection ) ) );

    return CAPPresentationCategoryMorphism( presentation_object,
                                            cokernel_projection,
                                            range_object,
                                            CapCategory( presentation_object )!.constructor_checks_wished
                                           );

end );



####################################################################################
##
#! @Section Minimal free resolutions
##
####################################################################################

# compute a minimal free resolution of a graded module presentation
InstallMethod( MinimalFreeResolutionForCAP,
               "for a CAPPresentationCategoryObject",
               [ IsGradedLeftOrRightModulePresentationForCAP ],
  function( presentation_object )
    local proj_category, left, morphisms, new_mapping_matrix, buffer_mapping, kernel_matrix, i, pos;

    # gather necessary information
    proj_category := CapCategory( UnderlyingMorphism( presentation_object ) );
    left := IsCAPCategoryOfProjectiveGradedLeftModulesMorphism( UnderlyingMorphism( presentation_object ) );

    # initialise morphisms
    morphisms := [];

    # use a presentation that does not contain units -> minimal (!) resolution
    if left then
      new_mapping_matrix := ReducedBasisOfRowModule( UnderlyingHomalgMatrix( 
                                                                          UnderlyingMorphism( presentation_object ) ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeLeft( new_mapping_matrix, 
                                                                    Range( UnderlyingMorphism( presentation_object ) ) );
    else
      new_mapping_matrix := ReducedBasisOfColumnModule( UnderlyingHomalgMatrix(
                                                                           UnderlyingMorphism( presentation_object ) ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeRight( new_mapping_matrix,
                                                                    Range( UnderlyingMorphism( presentation_object ) ) );
    fi;

    # and use this mapping as the first morphisms is the minimal free resolution
    Add( morphisms, buffer_mapping );

    # now compute "reduced" kernels
    if left then
      kernel_matrix := ReducedSyzygiesOfRows( UnderlyingHomalgMatrix( morphisms[ 1 ] ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeLeft( kernel_matrix, Source( morphisms[ 1 ] ) );      
    else
      kernel_matrix := ReducedSyzygiesOfColumns( UnderlyingHomalgMatrix( morphisms[ 1 ] ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeRight( kernel_matrix, Source( morphisms[ 1 ] ) );
    fi;

    # as long as the kernel is non-zero
    while not IsZeroForMorphisms( buffer_mapping ) do

      # add the corresponding kernel embedding
      Add( morphisms, buffer_mapping );

      # and compute the next kernel_embedding
      if left then
        kernel_matrix := ReducedSyzygiesOfRows( UnderlyingHomalgMatrix( buffer_mapping ) );
        buffer_mapping := DeduceMapFromMatrixAndRangeLeft( kernel_matrix, Source( buffer_mapping ) );
      else
        kernel_matrix := ReducedSyzygiesOfColumns( UnderlyingHomalgMatrix( buffer_mapping ) );
        buffer_mapping := DeduceMapFromMatrixAndRangeRight( kernel_matrix, Source( buffer_mapping ) );
      fi;

    od;

    # and return the corresponding complex
    return ComplexFromMorphismList( morphisms );

end );

# compute a minimal free resolution of a graded module presentation
InstallMethod( MinimalFreeResolutionForCAP,
               "for a CAPPresentationCategoryObject",
               [ IsGradedLeftOrRightSubmoduleForCAP and IsGradedLeftOrRightModulePresentationForCAP ],
  function( submodule_for_CAP )

    return MinimalFreeResolutionForCAP( PresentationForCAP( submodule_for_CAP ) );

end );



####################################################################################
##
#! @Section Full information about complex
##
####################################################################################

# compute a minimal free resolution of a graded module presentation
InstallMethod( FullInformation,
               "for a complex",
               [ IsCapComplex ],
  function( cocomplex )
    local differential_function, pos;

    # extract the differentials
    differential_function := UnderlyingZFunctorCell( cocomplex )!.differential_func;

    # start to print information
    pos := -1;
    
    while not IsZeroForObjects( Source( differential_function( pos ) ) ) do
    
      # print information
      Print( String( DegreeList( Range( differential_function( pos ) ) ) ) );
      Print( "\n" );
      Print( " ^ \n" );
      Print( " | \n" );
      Display( UnderlyingHomalgMatrix( differential_function( pos ) ) );
      Print( " | \n" );
      
      # increment
      pos := pos - 1;
    
    od;
    
    Print( String( DegreeList( Range( differential_function( pos ) ) ) ) );
    Print( "\n \n" );

end );



####################################################################################
##
#! @Section Betti tables
##
####################################################################################

# compute a minimal free resolution of a graded module presentation
InstallMethod( BettiTableForCAP,
               "for a CAPPresentationCategoryObject",
               [ IsGradedLeftOrRightModulePresentationForCAP ],
  function( presentation_object )
    local proj_category, left, betti_table, new_mapping_matrix, buffer_mapping, kernel_matrix, i, pos;

    # gather necessary information
    proj_category := CapCategory( UnderlyingMorphism( presentation_object ) );
    left := IsCAPCategoryOfProjectiveGradedLeftModulesMorphism( UnderlyingMorphism( presentation_object ) );

    # initialise morphisms
    betti_table := [];

    # use a presentation that does not contain units -> minimal (!) resolution
    if left then
      new_mapping_matrix := ReducedBasisOfRowModule( UnderlyingHomalgMatrix( UnderlyingMorphism( presentation_object ) ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeLeft( new_mapping_matrix, Range( UnderlyingMorphism( presentation_object ) ) );
    else
      new_mapping_matrix := ReducedBasisOfColumnModule( UnderlyingHomalgMatrix( UnderlyingMorphism( presentation_object ) ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeRight( new_mapping_matrix, Range( UnderlyingMorphism( presentation_object ) ) );
    fi;

    # and use this mapping as the first morphisms is the minimal free resolution
    Add( betti_table, UnzipDegreeList( Range( buffer_mapping ) ) );

    # check if we are already done
    if IsZeroForObjects( Source( buffer_mapping ) ) then
      return betti_table;
    fi;

    # otherwise add the source and compute the next mapping
    Add( betti_table, UnzipDegreeList( Source( buffer_mapping ) ) );

    # now compute "reduced" kernels
    if left then
      kernel_matrix := ReducedSyzygiesOfRows( UnderlyingHomalgMatrix( buffer_mapping ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeLeft( kernel_matrix, Source( buffer_mapping ) );
    else
      kernel_matrix := ReducedSyzygiesOfColumns( UnderlyingHomalgMatrix( buffer_mapping ) );
      buffer_mapping := DeduceMapFromMatrixAndRangeRight( kernel_matrix, Source( buffer_mapping ) );
    fi;

    # as long as the kernel is non-zero
    while not IsZeroForObjects( Source( buffer_mapping ) ) do

      # add the corresponding kernel embedding
      Add( betti_table, UnzipDegreeList( Source( buffer_mapping ) ) );

      # and compute the next kernel_embedding
      if left then
        kernel_matrix := ReducedSyzygiesOfRows( UnderlyingHomalgMatrix( buffer_mapping ) );
        buffer_mapping := DeduceMapFromMatrixAndRangeLeft( kernel_matrix, Source( buffer_mapping ) );
      else
        kernel_matrix := ReducedSyzygiesOfColumns( UnderlyingHomalgMatrix( buffer_mapping ) );
        buffer_mapping := DeduceMapFromMatrixAndRangeRight( kernel_matrix, Source( buffer_mapping ) );
      fi;

    od;

    # and return the Betti table
    return betti_table;

end );

InstallMethod( BettiTableForCAP,
               "for a graded submodule",
               [ IsGradedLeftOrRightSubmoduleForCAP ],
  function( submodule )
  
    return BettiTableForCAP( PresentationForCAP( submodule ) );

end );



####################################################################################
##
#! @Section Extension modules
##
####################################################################################

InstallMethod( GradedExtForCAP,
               "for an integer and two graded modules",
               [ IsInt, IsGradedLeftOrRightModulePresentationForCAP, IsGradedLeftOrRightModulePresentationForCAP ],
  function( i, module1, module2 )
    local left, mu, graded_hom_mapping;

    # check input
    left := IsGradedLeftModulePresentationForCAP( module1 );
    if i < 0 then
      Error( "the integer i must be non-negative" );
      return;
    elif IsGradedLeftModulePresentationForCAP( module2 ) <> left then
      Error( "the two modules must either both be left or both be right modules" );
      return;
    fi;

    # now compute the extension module

    # (1) extract the i-th morphism from a resolution of module1 (if i = 0, then this is to be taken as the zero morphism)
    if i = 0 then
      mu := ZeroMorphism( module1, ZeroObject( CapCategory( module1 ) ) );
    #elif i = 1 then
    #  mu := UnderlyingZFunctorCell( MinimalFreeResolutionForCAP( module1 ) )!.differential_func( -i );
    #  mu := ApplyFunctor( EmbeddingOfProjCategory( CapCategory( mu ) ), mu );
    #  mu := KernelEmbedding( CokernelProjection( mu ) );
    else
      mu := UnderlyingZFunctorCell( MinimalFreeResolutionForCAP( module1 ) )!.differential_func( -i );
      mu := ApplyFunctor( EmbeddingOfProjCategory( CapCategory( mu ) ), mu );
      mu := KernelEmbedding( CokernelProjection( mu ) );
    fi;

    # (2) compute GradedHom( Range( mu ), module2 ) -> GradedHom( Source( mu ), module2 )
    graded_hom_mapping := InternalHomOnMorphisms( mu, IdentityMorphism( module2 ) );

    # (3) then return the cokernel object of this morphism
    return CokernelObject( graded_hom_mapping );

end );

InstallMethod( GradedExtForCAP,
               "for an integer and two graded modules",
               [ IsInt, IsGradedLeftOrRightSubmoduleForCAP, IsGradedLeftOrRightModulePresentationForCAP ],
  function( i, module1, module2 )
    
    return GradedExtForCAP( i, PresentationForCAP( module1 ), module2 );

end );

InstallMethod( GradedExtForCAP,
               "for an integer and two graded modules",
               [ IsInt, IsGradedLeftOrRightModulePresentationForCAP, IsGradedLeftOrRightSubmoduleForCAP ],
  function( i, module1, module2 )

    return GradedExtForCAP( i, module1, PresentationForCAP( module2 ) );

end );

InstallMethod( GradedExtForCAP,
               "for an integer and two graded modules",
               [ IsInt, IsGradedLeftOrRightSubmoduleForCAP, IsGradedLeftOrRightSubmoduleForCAP ],
  function( i, module1, module2 )

    return GradedExtForCAP( i, PresentationForCAP( module1 ), PresentationForCAP( module2 ) );

end );



####################################################################################
##
#! @Section Twisting graded module presentations
##
####################################################################################

InstallMethod( Twist,
               "for a graded left or right module presentation and a list of integers",
               [ IsGradedLeftOrRightModulePresentationForCAP, IsList ],
  function( module, twist )
    local degree_group, k, left, new_range_degrees, new_range, matrix;

    # check that the twist has the correct length to belong to the degree group of the ring over which the module is defined
    degree_group := DegreeGroup( UnderlyingHomalgGradedRing( UnderlyingMorphism( module ) ) );
    if Length( twist ) <> Rank( degree_group ) then

      Error( "The given list cannot be interpreted as an element of the degree group of the graded ring which the module is defined over" );
      return;

    fi;

    # check that the entries of the twist are all integers
    for k in [ 1 .. Length( twist ) ] do

      if not IsInt( twist[ k ] ) then

        Error( "The entries of the given twist-list must be integers" );
        return;

      fi;

    od;

    # have to differ left and right module presentations eventually
    left := IsGradedLeftModulePresentationForCAP( module );

    # now perform the twist by subtracting twist from all generators and relations of the module
    new_range_degrees := List( [ 1 .. Length( DegreeList( Range( UnderlyingMorphism( module ) ) ) ) ],
                                k -> [ UnderlyingListOfRingElements( DegreeList( Range( UnderlyingMorphism( module ) ) )[ k ][ 1 ] ) - twist,
                                       DegreeList( Range( UnderlyingMorphism( module ) ) )[ k ][ 2 ] ] );

    # compute the new range object and deduce the mapping matrix
    if left then
      new_range := CAPCategoryOfProjectiveGradedLeftModulesObject( new_range_degrees,
                                                                   UnderlyingHomalgGradedRing( UnderlyingMorphism( module ) ) 
                                                                  );
    else
      new_range := CAPCategoryOfProjectiveGradedRightModulesObject( new_range_degrees,
                                                                    UnderlyingHomalgGradedRing( UnderlyingMorphism( module ) ) 
                                                                   );
    fi;
    matrix := UnderlyingHomalgMatrix( UnderlyingMorphism( module ) );

    # then compute the new module presentation from new_range and matrix and return the result
    if left then
      return CAPPresentationCategoryObject( DeduceMapFromMatrixAndRangeLeft( matrix , new_range ) );
    else
      return CAPPresentationCategoryObject( DeduceMapFromMatrixAndRangeRight( matrix , new_range ) );
    fi;

end );

InstallMethod( Twist,
               "for a graded left or right module presentation and a list of integers",
               [ IsGradedLeftOrRightModulePresentationForCAP, IsHomalgModuleElement ],
  function( module, twist )

    return Twist( module, UnderlyingListOfRingElements( twist ) );

end );