library(igraph)
#generates a connectivity matrix for SBM with n communities
generate_diagonal_pm<-function(p_diag,p_off,n){
  x=diag(p_diag,nrow=n)
  for (i in 1:n){
    for (j in 1:n){
      if (i==j){
        x[i,j]=x[i,j]
      }
      else{
        x[i,j]=p_off
      }
    }
  }
  return(x)
}


#Generate 2 kernel matrices for SBM data 
#takes diagonal probability before and after tau
#off-diagonal before and after tau
#n1 first segment length
#n2 total length
#b1 b2 vector of block sizes for each community before and after
#returns 2 kernel matrices: Gaussian and Graphlet
generate_toy_data<-function(p1_diag,p2_diag,p1_off,p2_off,n1,n2,b1,b2){
      G=list()
 
      block1=b1
      block2=b2
      
      pm1<-generate_diagonal_pm(p1_diag,p1_off,length(block1))
      pm2<-generate_diagonal_pm(p2_diag,p2_off,length(block2))
      #pm1 <- matrix(c(0.5,0.1,0.1,0.5),nrow=2)
      #pm2 <- matrix(c(0.5,0.1,0.1,0.5),nrow=2)
      
      adj=c()
      for ( i in 1:n1){
        #graphs for graphlet kernel
        
        g=sample_sbm(sum(block1), pref.matrix=pm1, block.sizes=block1, directed = FALSE, loops = FALSE)
        g=set_graph_attr(g,"label", value = seq(1:(sum(block1))))
        g<- delete_graph_attr(g, "loops")
        #g=set_vertex_attr(g,"label", value = c(rep(1,12),rep(2,12),rep(3,12),rep(4,14))) 
        #g=set_vertex_attr(g,"label", value = c(rep(1,block1[1]),rep(2,block1[2])))
        G[[i]]=g
        
        #get adjacecy matrix
        y1=as_adjacency_matrix(
          g,
          type = "both",
          attr = NULL,
          names = TRUE
        )
        m=matrix(y1,nrow=sum(block1))
        upper_triangular=m[upper.tri(m,diag=FALSE)]
        
        adj=rbind(adj,c(upper_triangular))
        
      }
      adj2=c()
      for ( i in (n1+1):n2){
        
        g2=sample_sbm(sum(block2), pref.matrix=pm2, block.sizes=block2, directed = FALSE, loops = FALSE)
        g2=set_graph_attr(g2,"label", value = seq(1:sum(block2)))
        g2<- delete_graph_attr(g2, "loops")
        #g2=set_vertex_attr(g2,"label", value = c(rep(1,12),rep(2,12),rep(3,18),rep(4,8)))
        #g2=set_vertex_attr(g2,"label", value = c(rep(1,block2[1]),rep(2,block2[2])))
        G[[i]]=g2
        y2=as_adjacency_matrix(
          g2,
          type = "both",
          attr = NULL,
          names = TRUE
        )
        m2=matrix(y2,nrow=sum(block2))
        upper_triangular2=m2[upper.tri(m2,diag=FALSE)]
        adj2=rbind(adj2,c(upper_triangular2))
        
      }
      
      adj3=rbind(adj,adj2)
      K1=gaussiankernel(adj3)
      K2=CalculateGraphletKernel(G,3)
      diag(K2)=0
      return(list(K1,K2))
}


vecU_row_to_sym <- function(v, n = NULL, diag_in_vector = FALSE, diag_value = 0) {
  m <- length(v)
  if (is.null(n)) {
    # infer n from m
    if (diag_in_vector) {
      n <- as.integer((-1 + sqrt(1 + 8*m)) / 2)
      stopifnot(m == n*(n+1)/2)
    } else {
      n <- as.integer((1 + sqrt(1 + 8*m)) / 2)
      stopifnot(m == n*(n-1)/2)
    }
  }
  S <- matrix(0, n, n)
  # coordinates of upper triangle in row-major order
  idx <- which(upper.tri(S, diag = diag_in_vector), arr.ind = TRUE)
  if (diag_in_vector) {
    ord <- order(idx[,1], idx[,2])          # row-major incl. diag
  } else {
    ord <- order(idx[,1], idx[,2])          # row-major excl. diag
  }
  idx <- idx[ord, , drop = FALSE]
  
  # fill and mirror
  S[idx] <- v
  S[lower.tri(S)] <- t(S)[lower.tri(S)]
  if (!diag_in_vector) diag(S) <- diag_value
  return(S)
}



shuffle_num <- function(x,k) {
  n <- length(x)
  stopifnot(n >= 2)
  idx <- sample.int(n, k)         # which positions to shuffle
  x[idx] <- sample(x[idx])        # permute only those positions
  return(x)
}



generate_SBM_switch_memberships<-function(conn_vec1,conn_vec2,n1,n2,Node,block_num,num_membership_switch){
  G=list()
  conn1_mat =  matrix(conn_vec1, nrow = block_num) 
  # connectivity matrix for the second segment 
  conn2_mat =  matrix(conn_vec2, nrow = block_num) 
  
  can_vec1 = sample(1:Node, replace = FALSE)
  can_vec2=shuffle_num(can_vec1,num_membership_switch)
  sbm1 = simu.SBM(conn1_mat, can_vec1, n1, symm = TRUE, self = FALSE) 
  sbm2 = simu.SBM(conn2_mat, can_vec2, n2, symm = TRUE, self = FALSE) 
  data_mat = rbind(t(sbm1$obs_mat), t(sbm2$obs_mat))
  
  K1=gaussiankernel(data_mat)
  
  for (i in 1:n1){
    adj=vecU_row_to_sym(data_mat[i,])
    rownames(adj) <- colnames(adj) <- can_vec1
    g=graph_from_adjacency_matrix(adj)
    G[[i]]=g
  }
  for (j in (n1+1):nrow(data_mat)){
    adj=vecU_row_to_sym(data_mat[j,])
    rownames(adj) <- colnames(adj) <- can_vec2
    g2=graph_from_adjacency_matrix(adj)
    G[[j]]=g2
  }
  K2=CalculateGraphletKernel(G,3)
  diag(K2)=0
  return(list(K1,K2))
}


#Random Geometric Graph data 
#radius before and after tau
#n1 first segment length
#n2 total length
#Torus: true or false
#returns 2 kernel matrices: Gaussian and Graphlet
generate_rgg_data<-function(r1,r2,n1,n2,torus,N){
      G=list()
      adj=c()
      for ( i in 1:n1){
        #graphs for graphlet kernel
        g=sample_grg(n = N, radius = r1, coords = TRUE,torus=torus)
        g=set_graph_attr(g,"label", value = seq(1:N))
        #g<- delete_graph_attr(g, "loops")
        #g=set_vertex_attr(g,"label", value = c(rep(1,b1[1]),rep(2,b1[2])))
        G[[i]]=g
        
        #get adjacecy matrix
        y1=as_adjacency_matrix(
          g,
          type = "both",
          attr = NULL,
          names = TRUE
        )
        adj=rbind(adj,c(matrix(y1)))
        
      }
      adj2=c()
      for ( i in (n1+1):n2){
        g2=sample_grg(n = N, radius = r2, coords = TRUE,torus=torus)
        g2=set_graph_attr(g2,"label", value = seq(1:N))
        #g2<- delete_graph_attr(g2, "loops")
        #g2=set_vertex_attr(g2,"label", value = c(rep(1,12),rep(2,12),rep(3,18),rep(4,8)))
        #g2=set_vertex_attr(g2,"label", value = c(rep(1,b1[1]),rep(2,b1[2])))
        G[[i]]=g2
        y2=as_adjacency_matrix(
          g2,
          type = "both",
          attr = NULL,
          names = TRUE
        )
        adj2=rbind(adj2,c(matrix(y2)))
      }
      adj3=rbind(adj,adj2)
      K1=gaussiankernel(adj3)
      K2=CalculateGraphletKernel(G,3)
      diag(K2)=0
      return(list(K1,K2))
}

#Exponential Random Graph Model 
# before and after tau
#n1 first segment length
#n2 total length
#returns 2 kernel matrices: Gaussian and Graphlet
generate_ergm_data<-function(nodes,c1,c2,n1,n2){
      G=list()
      adj=c()
      
      for (i in 1:n1){
        g <- network.initialize(nodes, directed = FALSE)
        sim_net <- simulate(
          g ~ edges + triangles,
          coef = c1,
          nsim = 1,
          control = control.simulate.formula(MCMC.burnin = 20000)
        )
        adj_mat <- as.matrix.network(sim_net, matrix.type = "adjacency")
        adj=rbind(adj,c(adj_mat))
        G[[i]]=graph_from_adjacency_matrix(adj_mat, mode = "undirected") 
      }
      
      
      for (j in (n1+1):n2){
        
        g2 <- network.initialize(nodes, directed = FALSE)
        sim_net2 <- simulate(
          g2 ~ edges + triangles,
          coef = c2,
          nsim = 1,
          control = control.simulate.formula(MCMC.burnin = 20000)
        )
        adj_mat <- as.matrix.network(sim_net2, matrix.type = "adjacency")
        adj=rbind(adj,c(adj_mat))
        G[[j]]=graph_from_adjacency_matrix(adj_mat, mode = "undirected") 
        
      }
      
      K2=CalculateGraphletKernel(G,3)
      diag(K2)=0
      K1=gaussiankernel(adj)
      return(list(K1,K2))
}




#SBM but gives adjacency matrices instead of Kernels
generate_adjacency_matrix<-function(p1_diag,p2_diag,p1_off,p2_off,n1,n2,b1,b2){
      G=list()
      #block1=c(25,25)
      #block2=c(25,25)
      block1=b1
      block2=b2
      
      pm1<-generate_diagonal_pm(p1_diag,p1_off,length(b1))
      pm2<-generate_diagonal_pm(p2_diag,p2_off,length(b2))
      #pm1 <- matrix(c(0.5,0.1,0.1,0.5),nrow=2)
      #pm2 <- matrix(c(0.5,0.1,0.1,0.5),nrow=2)
      
      adj=c()
      for ( i in 1:n1){
        #graphs for graphlet kernel
        g=sample_sbm(sum(b1), pref.matrix=pm1, block.sizes=block1, directed = FALSE, loops = FALSE)
        g=set_graph_attr(g,"label", value = seq(1:(sum(b1))))
        g<- delete_graph_attr(g, "loops")
        g=set_vertex_attr(g,"label", value = c(rep(1,10),rep(2,10),rep(3,10))) 
        #g=set_vertex_attr(g,"label", value = c(rep(1,b1[1]),rep(2,b1[2])))
        G[[i]]=g
        
        #get adjacecy matrix
        y1=as_adjacency_matrix(
          g,
          type = "both",
          attr = NULL,
          names = TRUE
        )
        adj=c(adj,c(matrix(y1)))
        
      }
      
      
      adj2=c()
      for ( i in (n1+1):n2){
        g2=sample_sbm(sum(b2), pref.matrix=pm2, block.sizes=block2, directed = FALSE, loops = FALSE)
        g2=set_graph_attr(g2,"label", value = seq(1:sum(b2)))
        g2<- delete_graph_attr(g2, "loops")
        g2=set_vertex_attr(g2,"label", value = c(rep(1,10),rep(2,10),rep(3,10)))
        #g2=set_vertex_attr(g2,"label", value = c(rep(1,b1[1]),rep(2,b1[2])))
        G[[i]]=g2
        y2=as_adjacency_matrix(
          g2,
          type = "both",
          attr = NULL,
          names = TRUE
        )
        adj=c(adj,c(matrix(y2)))
        
      }
      
      adj3<- matrix(adj, nrow=100,ncol=900)
      
      
      return(adj3)
}