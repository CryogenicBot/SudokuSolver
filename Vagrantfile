$prov_script = <<-SCRIPT
echo I am provisioning...
sudo apt-get update
sudo apt-get -y install haskell-platform
curl -sSL https://get.haskellstack.org/ | sh
PATH="$PATH:/usr/local/bin"
SCRIPT

Vagrant.configure("2") do |config|

    config.vm.box = "ubuntu/xenial64"

    config.vm.provider "virtualbox" do |vb|
        vb.gui = false
        vb.customize ["modifyvm", :id, "--memory", "8192"]
        vb.customize ["modifyvm", :id, "--cpus", 2]
        vb.customize ["modifyvm", :id, "--natdnshostresolver1", "on"]
        vb.customize ["modifyvm", :id, "--uartmode1", "disconnected"]
    end

    config.vm.provision "shell", inline: $prov_script  

end