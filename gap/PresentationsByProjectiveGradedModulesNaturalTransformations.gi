#############################################################################
##
## PresentationsByProjectiveGradedModules
##
## Copyright 2019,  Martin Bies,       ULB Brussels
##
## Chapter Natural transformations for graded module presentations for CAP
##
#############################################################################


####################################################################################
##
##  Section Natural isomorphism from identity functor to the standard module functor
##
####################################################################################

# a function that computes the natural isomorphism 1 => StandardModule for both
# left and right presentations
InstallGlobalFunction( NaturalIsomorphismFromIdentityToGradedStandardModule,
  function( graded_ring, left )
    local category, standard_module_functor, natural_transformation;

    if left = true then
      category := SfpgrmodLeft( graded_ring );
      standard_module_functor := FunctorGradedStandardModuleLeft( graded_ring );
    else
      category := SfpgrmodRight( graded_ring );
      standard_module_functor := FunctorGradedStandardModuleRight( graded_ring );
    fi;

    # initialise the natural_transformation
    natural_transformation := NaturalTransformation( Concatenation( "Natural isomorphism from Id to ",
                                                     Name( standard_module_functor ) ),
                                                     IdentityMorphism( AsCatObject( category ) ),
                                                     standard_module_functor 
                                                    );

    # add component of natural_transformation over object
    AddNaturalTransformationFunction( natural_transformation,
      function( id_object, object, standard_object )
        local matrix, underlying_morphism;

        matrix := HomalgIdentityMatrix( Rank( Range( UnderlyingMorphism( id_object ) ) ), graded_ring );

        underlying_morphism := CAPCategoryOfProjectiveGradedLeftOrRightModulesMorphism(
                                                      Range( UnderlyingMorphism( id_object ) ),
                                                      matrix,
                                                      Range( UnderlyingMorphism( standard_object ) ),
                                                      CapCategory( UnderlyingMorphism( id_object ) )!.constructor_checks_wished 
                                                     );

        return CAPPresentationCategoryMorphism( id_object, 
                                                underlying_morphism, 
                                                standard_object,
                                                CapCategory( id_object )!.constructor_checks_wished 
                                               );

    end );

    # inform CAP that this is a natural isomorphism
    SetIsIsomorphism( natural_transformation, true );

    # and finally return this transformation
    return natural_transformation;

end );

# natural isomorphism 1 => Standard module for left presentations
InstallMethod( NaturalIsomorphismFromIdentityToGradedStandardModuleLeft,
               [ IsHomalgGradedRing ],
  function( graded_ring )

    return NaturalIsomorphismFromIdentityToGradedStandardModule( graded_ring, true );

end );

# natural isomorphism 1 => Standard module for right presentations
InstallMethod( NaturalIsomorphismFromIdentityToGradedStandardModuleRight,
               [ IsHomalgGradedRing ],
  function( graded_ring )

    return NaturalIsomorphismFromIdentityToGradedStandardModule( graded_ring, false );

end );