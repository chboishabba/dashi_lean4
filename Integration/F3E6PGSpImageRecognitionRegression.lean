import Integration.F3E6PGSpImageRecognition

namespace DASHI.Integration.F3E6PGSpImageRecognitionRegression

open F3E6PGSpImageRecognition

example : projectiveFiveImage.card = 51840 := projectiveFiveImage_card
example : e6GeneratedClosure.card = 51840 := e6GeneratedClosure_card
example : projectiveFiveImage = e6GeneratedClosure := projectiveFiveImage_eq_e6GeneratedClosure

example :
    DASHI.Integration.F3FourSymplecticExteriorSquare.PGSpWeylRecognition :=
  commonMatrixImageRecognition

example : imageRecognitionBoundary.literalFiveMatrixImageEqualityPaid = true := rfl
example : imageRecognitionBoundary.sameActionImageRecognitionPaid = true := rfl
example : imageRecognitionBoundary.pgspWeylRecognitionInhabitedAtMatrixImage = true := rfl
example : imageRecognitionBoundary.abstractPGSp4QuotientWeylGroupIsomorphismPaid = false := rfl

end DASHI.Integration.F3E6PGSpImageRecognitionRegression
