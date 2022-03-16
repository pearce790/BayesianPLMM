### Mollica and Tardella (2017) ####
### Packages ####
library(label.switching)
library(gtools)
library(matrixStats)
library(ggplot2)

### Functions ####
Rpl <- function(n_s,p){
  sample(1:K,size=n_s,replace=FALSE,prob=p)
}
Ppl <- function(pi,p,log=FALSE){
  ## pi is a (partial) ordering
  ## p is a support parameter for all possible objects
  num <- p[pi]
  denom <- sum(p)-c(0,cumsum(p[pi][-length(pi)]))
  if(log){return(sum(log(num)-log(denom)))
  }else{return(prod(num/denom))}
}
EM <- function(piinv,N,K,G,n_s,c,d,alpha,tol=0.001){
  #pre-computation
  u <- matrix(0,nrow=N,ncol=K)
  for(s in 1:N){for(i in 1:K){u[s,i] <- as.numeric(i %in% piinv[s,])}}
  delta <- array(0,dim=c(N,K,K))
  delta[,1,] <- 1
  for(s in 1:N){for(t in 2:K){for(i in 1:K){
    delta[s,t,i] <- 1- as.numeric(i %in% piinv[s,1:(t-1)])
  }}}
  
  # initialize
  pstar <- matrix(runif(G*K),ncol=G)
  omegastar <- rep(1/G,G)
  zhat <- matrix(0,nrow=N,ncol=G)
  gammahat <- matrix(0,nrow=G,ncol=K)
  
  pnew <- matrix(1000,nrow=K,ncol=G)
  omeganew <-rep(1000,G)
  diff <- sum(abs(pnew-pstar))+sum(abs(omeganew-omegastar))
  
  while(diff > tol){
    # E Step 
    for(s in 1:N){
      zhat_probs <- unlist(lapply(1:G,function(g){Ppl(piinv[s,piinv[s,]>0],pstar[,g])}))
      zhat[s,] <- omegastar*zhat_probs/sum(omegastar*zhat_probs)
    }
    for(g in 1:G){for(i in 1:K){gammahat[g,i] <- sum(zhat[,g]*u[,i])}}
    
    # M Step
    for(g in 1:G){for(i in 1:K){
      num <- c[g,i] - 1 + gammahat[g,i]
      denom <- d[g] + sum(unlist(lapply(1:N,function(s){
        zhat[s,g]*sum(unlist(lapply(1:n_s[s],function(t){delta[s,t,i]/sum(delta[s,t,]*pstar[,g])})))
      })))
      pnew[i,g] <- num/denom
    }}
    for(g in 1:G){
      num <- alpha[g] - 1 + sum(zhat[,g])
      denom <- sum(alpha)-G+N
      omeganew[g] <- num/denom
    }
    diff <- mean(c(abs(pnew-pstar),abs(omeganew-omegastar)))
    pstar <- pnew
    omegastar <- omeganew
  }
  
  return(list(pstar = pstar, omegastar = omegastar))
}
gibbs <- function(piinv,num_iters,N,K,G,n_s,c,d,alpha,
                  pstar,omegastar,verbose=TRUE){
  z.out <- matrix(0,nrow=num_iters,ncol=N)
  p.out <- array(0,c(num_iters,K,G))
  omega.out <- matrix(0,nrow=num_iters,ncol=G)
  pcurr <- pstar
  omegacurr <- omegastar
  y <- matrix(0,nrow=N,ncol=K)
  z <- matrix(NA,nrow=N,ncol=G)
  
  u <- matrix(0,nrow=N,ncol=K)
  for(s in 1:N){for(i in 1:K){u[s,i] <- as.numeric(i %in% piinv[s,])}}
  delta <- array(0,dim=c(N,K,K))
  delta[,1,] <- 1
  for(s in 1:N){for(t in 2:K){for(i in 1:K){
    delta[s,t,i] <- 1- as.numeric(i %in% piinv[s,1:(t-1)])
  }}}
  gammahat <- matrix(0,nrow=G,ncol=K)
  
  label_probs <- array(0,dim=c(num_iters,N,G))
  
  for(iter in 1:num_iters){
    if(iter %% 1000 == 0){print(paste0("Iteration ",iter," of ",num_iters))}
    for(s in 1:N){
      probs <- unlist(lapply(1:G,function(g){
        omegacurr[g]*prod(unlist(lapply(1:K,function(i){
          pcurr[i,g]^u[s,i]*exp(-pcurr[i,g]*sum(delta[s,1:n_s[s],i]*y[s,1:n_s[s]]))
        })))
      }))
      z[s,] <- c(rmultinom(1,1,probs/sum(probs)))
      label_probs[iter,s,] <- probs/sum(probs)
    }
    for(g in 1:G){for(i in 1:K){gammahat[g,i] <- sum(z[,g]*u[,i])}}
    for(g in 1:G){
      for(i in 1:K){
        pcurr[i,g] <- rgamma(1,c[g,i]+gammahat[g,i],
                             d[g]+sum(unlist(lapply(1:N,function(s){z[s,g]*sum(delta[s,1:n_s[s],i]*y[s,1:n_s[s]])}))))
      }
      pcurr[,g] <- pcurr[,g]/sum(pcurr[,g])
    }
    omegacurr <- c(rdirichlet(1,alpha+apply(z,2,sum)))
    
    for(s in 1:N){for(t in 1:n_s[s]){
      z_curr <- which(z[s,]==1)
      rate <- sum(pcurr[,z_curr])-sum(pcurr[piinv[s,1:(t-1)],z_curr])
      y[s,t] <- rexp(1,rate)
    }}
    z.out[iter,] <- apply(z,1,function(x){which(x==1)})
    p.out[iter,,] <- pcurr
    omega.out[iter,] <- omegacurr
  }
  
  #label swapping
  if(G>1){
    labels <- stephens(label_probs)
    for(iter in 1:num_iters){
      p.out[iter,,]  <- p.out[iter,,labels$permutations[iter,]]
      z.out[iter,] <- (labels$permutations[iter,])[z.out[iter,]]
      omega.out[iter,] <- omega.out[iter,labels$permutations[iter,]]
    }
  }
  
  #normalizing
  # for(g in 1:G){
  #   p.out[,,g] <- t(apply(p.out[,,g],1,function(x){x/sum(x)}))
  # }
  
  #return
  return(list(p.out = p.out, omega.out = omega.out,z.out = z.out))
}
get_logL <- function(piinv,p.out,omega.out){
  N <- nrow(piinv)
  G <- length(omega.out)
  logL <- sum(unlist(lapply(1:N,function(s){
    pi_s <- piinv[s,piinv[s,]>0]
    logSumExp(unlist(lapply(1:G,function(g){log(omega.out[g])+Ppl(pi_s,p.out[,g],log=T)})))
  })))
  return(logL)
}

### Simulation Study ####

#code below is ran on the cluster in parallel
for(G in 1:4){
  for(CensorSetting in 1:3){
    for(seed in 1:50){
      N <- 1000
      K <- 6
      if(CensorSetting == 1){n_s <- c(rep(2,20),rep(3,40),rep(4,100),rep(6,840))}
      if(CensorSetting == 2){n_s <- c(rep(1,50),rep(2,150),rep(3,150),rep(4,200),rep(6,450))}
      if(CensorSetting == 3){n_s <- c(rep(1,50),rep(2,200),rep(3,200),rep(4,250),rep(6,300))}
      p <- matrix(rbeta(G*K,.3,.3),ncol=G)
      omega <- rep(1/G,G)
      
      piinv <- matrix(0,nrow=N,ncol=K)
      for(s in 1:N){
        z <- sample(G,1,prob=omega)
        piinv[s,1:n_s[s]] <- Rpl(n_s[s],p[,z])
      }
      
      results <- data.frame(TrueG=rep(G,4),CensorSetting=rep(CensorSetting,4),
                            G=1:4,DIC1=NA,DIC2=NA,BICM1=NA,BICM2=NA,
                            BPIC1=NA,BPIC2=NA,BIC=NA)
      num_iters <- 4000
      for(G in 1:4){
        print(paste0("G = ",G))
        c <- matrix(1,nrow=G,ncol=K) #technically can be indexed by g and i
        d <- rep(.001,G) #technically can be indexed by g
        alpha <- rep(1,G)
        
        print("Starting EM")
        em_res <- EM(piinv,N,K,G,n_s,c,d,alpha)
        print("Starting Gibbs")
        gibbs_res <- gibbs(piinv,num_iters = num_iters,N,K,G,n_s,c,d,alpha,
                           pstar = em_res$pstar,omegastar = em_res$omegastar,verbose=T)
        gibbs_res$p.out <- gibbs_res$p.out[-c(1:(num_iters/2)),,]
        gibbs_res$omega.out <- as.matrix(gibbs_res$omega.out[-c(1:(num_iters/2)),],ncol=G)
        gibbs_res$z.out <- gibbs_res$z.out[-c(1:(num_iters/2)),]
        
        print("Getting Summary Stats")
        if(G == 1){
          logL <- unlist(lapply(1:nrow(gibbs_res$omega.out),function(iter){
            get_logL(piinv,p.out=matrix(gibbs_res$p.out[iter,],ncol=G),
                     omega.out=gibbs_res$omega.out[iter,])
          }))
        }else{
          logL <- unlist(lapply(1:nrow(gibbs_res$omega.out),function(iter){
            get_logL(piinv,matrix(gibbs_res$p.out[iter,,],ncol=G),gibbs_res$omega.out[iter,])
          }))
        }
        
        logL_map <- get_logL(piinv,em_res$pstar,em_res$omegastar)
        DIC1 <- -4*mean(logL)+2*logL_map
        DIC2 <- -2*mean(logL)+var(-2*logL)/2
        BICM1 <- -2*mean(logL)+(var(-2*logL)/2)*(log(N)-1)
        BICM2 <- -2*logL_map + (var(-2*logL)/2)*(log(N))
        BPIC1 <- -6*mean(logL)+4*logL_map
        BPIC2 <- -2*mean(logL)+var(-2*logL)
        BIC <- (G+G*K)*log(N)-2*logL_map
        results[G,4:10] <- c(DIC1,DIC2,BICM1,BICM2,BPIC1,BPIC2,BIC)
      }
      print(results) #table saved when running on cluster
    }
  }
}

#compiling simulation code
sim_results <- matrix(data=NA,nrow=0,ncol=9)
for(G in 1:4){
  for(CS in 1:3){
    true <- c(G,CS,rep(0,7))
    count <- 0
    for(seed in 1:60){
      tryCatch({
        load(paste0("project_sims/stat544_G",G,
                    "_CS",CS,"_seed",seed,".RData"))
        true[3:9] <- true[3:9] + (apply(results[,4:10],2,which.min) == G)
        count <- count+1
      },error=function(e){r},warning=function(e){})
    }
    true[3:9] <- true[3:9]/count
    sim_results <- rbind(sim_results,true)
  }
}
sim_results <- as.data.frame(sim_results)
names(sim_results) <- c("G","CS","DIC1","DIC2","BICM1","BICM2","BPIC1","BPIC2","BIC")
sim_results #compiled results


### CARCONF Data ####
library(prefmod) #load data
data("carconf")
data <- carconf[,1:6]

piinv <- t(apply(data,1,function(x){ #convert data into correct format
  ranking <- c(unlist(lapply(1:6,function(rank){
    which(x == rank)})))
  if(length(ranking < 6)){
    ranking <- c(ranking,rep(0,6-length(ranking)))
  }
  return(ranking)
}))

K <- 6 #set constants
N <- 435
n_s <- apply(piinv,1,function(pi){sum(pi>0)})

# run through G=1:6
results <- data.frame(G=1:6,DIC1=NA,DIC2=NA,BICM1=NA,BICM2=NA,
                      BPIC1=NA,BPIC2=NA,BIC=NA)
num_iters <- 2000
for(G in 1:6){
  print(paste0("G = ",G))
  c <- matrix(1,nrow=G,ncol=K) #technically can be indexed by g and i
  d <- rep(.001,G) #technically can be indexed by g
  alpha <- rep(1,G)
  
  print("Starting EM")
  em_res <- EM(piinv,N=435,K=6,G=G,n_s=n_s,c=c,d=d,alpha=alpha,tol=.001)
  print("Starting Gibbs")
  gibbs_res <- gibbs(piinv,num_iters = num_iters,N=435,K=6,G=G,n_s=n_s,c=c,d=d,alpha=alpha,
                     pstar = em_res$pstar,omegastar = em_res$omegastar,verbose=T)
  gibbs_res$p.out <- gibbs_res$p.out[-c(1:(num_iters/2)),,]
  gibbs_res$omega.out <- as.matrix(gibbs_res$omega.out[-c(1:(num_iters/2)),],ncol=G)
  gibbs_res$z.out <- gibbs_res$z.out[-c(1:(num_iters/2)),]
  
  print("Getting Summary Stats")
  if(G == 1){
    logL <- unlist(lapply(1:nrow(gibbs_res$omega.out),function(iter){
      get_logL(piinv,p.out=matrix(gibbs_res$p.out[iter,],ncol=G),
               omega.out=gibbs_res$omega.out[iter,])
    }))
  }else{
    logL <- unlist(lapply(1:nrow(gibbs_res$omega.out),function(iter){
      get_logL(piinv,matrix(gibbs_res$p.out[iter,,],ncol=G),gibbs_res$omega.out[iter,])
    }))
  }
  
  logL_map <- get_logL(piinv,em_res$pstar,em_res$omegastar)
  DIC1 <- -4*mean(logL)+2*logL_map
  DIC2 <- -2*mean(logL)+var(-2*logL)/2
  BICM1 <- -2*mean(logL)+(var(-2*logL)/2)*(log(N)-1)
  BICM2 <- -2*logL_map + (var(-2*logL)/2)*(log(N))
  BPIC1 <- -6*mean(logL)+4*logL_map
  BPIC2 <- -2*mean(logL)+var(-2*logL)
  BIC <- (G+G*K)*log(N)-2*logL_map
  
  results[G,2:8] <- c(DIC1,DIC2,BICM1,BICM2,BPIC1,BPIC2,BIC)
  print(results)
}

#examine model selection criteria
res_apa <- reshape2::melt(results,id="G")
ggplot(res_apa,aes(G,value,color=variable))+geom_line()+geom_point()+
  ylab("Selection Criterion")+theme(legend.position = "right")+
  scale_x_continuous(breaks=1:6)+
  labs(color="Criterion")

#get overall results for G=2
G <- 2
c <- matrix(1,nrow=G,ncol=K) #technically can be indexed by g and i
d <- rep(.001,G) #technically can be indexed by g
alpha <- rep(1,G)
set.seed(0)
em_res <- EM(piinv,N=435,K=6,G=G,n_s=n_s,c=c,d=d,alpha=alpha,tol=.0001)
num_iters <- 5000
gibbs_res <- gibbs(piinv,num_iters = num_iters,N=435,K=6,G=G,n_s=n_s,c=c,d=d,alpha=alpha,
                   pstar = em_res$pstar,omegastar = em_res$omegastar,verbose=T)
gibbs_res$p.out <- gibbs_res$p.out[-c(1:(num_iters/2)),,]
gibbs_res$omega.out <- as.matrix(gibbs_res$omega.out[-c(1:(num_iters/2)),],ncol=G)
gibbs_res$z.out <- gibbs_res$z.out[-c(1:(num_iters/2)),]

apa_bayes <- rbind(as.data.frame(t(as.data.frame(apply(gibbs_res$p.out[,,1],2,function(q){quantile(q,c(.025,.5,.975))})))),
                   as.data.frame(t(as.data.frame(apply(gibbs_res$p.out[,,2],2,function(q){quantile(q,c(.025,.5,.975))})))))
names(apa_bayes)<-c("low","med","upp")
apa_bayes$Group <- c(rep("1 (Weight=.32)",6),rep("2 (Weight=.68)",6))
apa_bayes$Item <- as.factor(rep(c("Price","Exterior","Brand","TechEquip","Country","Interior"),2))
p1<-ggplot(apa_bayes,aes(Item,med))+geom_point()+facet_wrap(vars(Group),nrow=1,labeller = label_both)+
  geom_errorbar(aes(ymin=low,ymax=upp))+
  theme(axis.text.x = element_text(angle = 45, vjust = 1, hjust=1))+
  ylab("Support Parameter")
pstar <- as.data.frame(em_res$pstar)
pstar$Item <- c("Price","Exterior","Brand","TechEquip","Country","Interior")
pstar$V1 <- pstar$V1/sum(pstar$V1)*em_res$omegastar[1]
pstar$V2 <- pstar$V2/sum(pstar$V2)*em_res$omegastar[2]
pstar <- reshape2::melt(pstar)
pstar$Item <- factor(pstar$Item)
pstar$Group <- factor(pstar$variable,levels=c("V2","V1"),labels=c(1,2))
p2<-ggplot(pstar)+geom_mosaic(mapping=aes(weight=value,x=product(Item,Group),fill=Item))+
  theme(legend.position = "none")+ylab("")
gridExtra::grid.arrange(p1,p2,ncol=2,widths=c(.56,.45))

### APA Data ####
library(ConsRank) #load data
data("APAFULL")

piinv <- t(apply(APAFULL,1,function(x){ #put data into correct format
  ranking <- c(unlist(lapply(1:5,function(rank){
    which(x == rank)})))
  if(length(ranking < 5)){
    ranking <- c(ranking,rep(0,5-length(ranking)))
  }
  return(ranking)
}))

# Try out G=1:12
results <- data.frame(G=1:12,DIC1=NA,DIC2=NA,BICM1=NA,BICM2=NA,
                      BPIC1=NA,BPIC2=NA,BIC=NA)
num_iters <- 4000
for(G in 1:12){ #run on cluster
  print(paste0("G = ",G))
  c <- matrix(1,nrow=G,ncol=K) #technically can be indexed by g and i
  d <- rep(.001,G) #technically can be indexed by g
  alpha <- rep(1,G)
  
  print("Starting EM")
  em_res <- EM(piinv,N=15449,K=5,G=G,n_s=n_s,c=c,d=d,alpha=alpha,tol=.1)
  print("Starting Gibbs")
  gibbs_res <- gibbs(piinv,num_iters = num_iters,N=15449,K=5,G=G,n_s=n_s,c=c,d=d,alpha=alpha,
                     pstar = em_res$pstar,omegastar = em_res$omegastar,verbose=T)
  gibbs_res$p.out <- gibbs_res$p.out[-c(1:(num_iters/2)),,]
  gibbs_res$omega.out <- as.matrix(gibbs_res$omega.out[-c(1:(num_iters/2)),],ncol=G)
  gibbs_res$z.out <- gibbs_res$z.out[-c(1:(num_iters/2)),]
  
  print("Getting Summary Stats")
  if(G == 1){
    logL <- unlist(lapply(1:nrow(gibbs_res$omega.out),function(iter){
      get_logL(piinv,p.out=matrix(gibbs_res$p.out[iter,],ncol=G),
               omega.out=gibbs_res$omega.out[iter,])
    }))
  }else{
    logL <- unlist(lapply(1:nrow(gibbs_res$omega.out),function(iter){
      get_logL(piinv,matrix(gibbs_res$p.out[iter,,],ncol=G),gibbs_res$omega.out[iter,])
    }))
  }
  
  logL_map <- get_logL(piinv,em_res$pstar,em_res$omegastar)
  DIC1 <- -4*mean(logL)+2*logL_map
  DIC2 <- -2*mean(logL)+var(-2*logL)/2
  BICM1 <- -2*mean(logL)+(var(-2*logL)/2)*(log(N)-1)
  BICM2 <- -2*logL_map + (var(-2*logL)/2)*(log(N))
  BPIC1 <- -6*mean(logL)+4*logL_map
  BPIC2 <- -2*mean(logL)+var(-2*logL)
  BIC <- (G+G*K)*log(N)-2*logL_map
  
  results[G,2:8] <- c(DIC1,DIC2,BICM1,BICM2,BPIC1,BPIC2,BIC)
  print(results)
}





