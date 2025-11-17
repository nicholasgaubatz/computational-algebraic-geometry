                                                  2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y , y , y , y )   }
                              1 2    1 3    2 3   1   2   3   4
                                2   2   2         2
          AOTinIdeal => ideal (y , y , y , y y , y )
                                4   3   2   1 2   1
          graph => {set {0, 5}, set {5, 6}, set {0, 6}, set {1, 6}}
                                2     3
          hSeries => 1 + 4T + 5T  + 2T
          hyperplanes => {a - f, f - g, a - g, b - g}
          numVariables => 4
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_4]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_2-y_1*y_3-y_2*y_3, y_1^2, y_2^2, y_3^2, y_4^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}},{{y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 5}, set {5, 6}, set {0, 6}, set {1, 6}}
