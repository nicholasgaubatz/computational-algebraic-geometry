                                 2   2
HashTable{AOTideal => ideal (0, y , y )       }
                                 1   2
                                2   2
          AOTinIdeal => ideal (y , y )
                                2   1
          graph => {set {0, 5}, set {1, 5}}
                               2
          hSeries => 1 + 2T + T
          hyperplanes => {a - f, b - f}
          numVariables => 2
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_2]
AOTideal = ideal map(R^1,R^{{0}, {-2}, {-2}},{{0, y_1^2, y_2^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}},{{y_2^2, y_1^2}})
G = graph {set {0, 5}, set {1, 5}}
