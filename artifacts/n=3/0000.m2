                                 2
HashTable{AOTideal => ideal (0, y )           }
                                 1
                               2
          AOTinIdeal => ideal y
                               1
          graph => {set {0, 2}}
          hSeries => 1 + T
          hyperplanes => {a - c}
          numVariables => 1
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1]
AOTideal = ideal map(R^1,R^{{0}, {-2}},{{0, y_1^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}},{{y_1^2}})
G = graph {set {0, 2}}
